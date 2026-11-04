module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow

/-!
# The Picard stack is fibred in groupoids (Stacks 04WN, condition (1))

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25.  Stacks 04WN asserts that the functor
`p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` of Section 0372, which sends an object `(U, b, L)` to its
test scheme `U`, defines a *stack in groupoids*.  This file proves the first of the three
conditions of Stacks 02ZI for that functor: it is fibred in groupoids.

The argument is the one of the source.  Existence of lifts: a morphism `h : V ⟶ U` of test
schemes over the base pulls an object `(U, b, L)` back to `(V, b ∘ h, (X_h)^*L)`, the comparison
of modules being the identity, and that triple is again an object because the inverse image of
an invertible module is invertible.  Existence and uniqueness of fill-ins: given
`(h₁, φ₁) : (U₁, b₁, L₁) ⟶ (U, b, L)`, `(h₂, φ₂) : (U₂, b₂, L₂) ⟶ (U, b, L)` and `h : U₁ ⟶ U₂`
with `h₂ ∘ h = h₁`, the fill-in is `h` together with the composite

`(X_h)^*L₂ ⟶ (X_h)^*(X_{h₂})^*L = (X_{h₁})^*L ⟶ L₁`

of the inverse image of `φ₂⁻¹`, the comparison of Stacks 03LU for the composite and `φ₁`; it is
the only fill-in because a morphism of `Picardstack_{X/B}` is determined by its base map and its
comparison of modules, and `φ₂` being an isomorphism makes the comparison of a composite
determine the comparison of its left factor.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.pullbackObject` and
  `AlgebraicGeometry.Space.PicardSituation.pullbackHom`: the pullback of an object of
  `Picardstack_{X/B}` along a morphism of test schemes, and the morphism of `Picardstack_{X/B}`
  it carries.
* `AlgebraicGeometry.Space.PicardSituation.fillIn`: the fill-in of the second half of the
  argument.

## Main results

* `AlgebraicGeometry.Space.picardProjection_isFiberedInGroupoids_schemesOver`: the projection of
  `Picardstack_{X/B}` to the *test schemes over the base* is fibred in groupoids.  This is the
  whole content; the assertion over the site follows by composing with the projection of the
  test schemes to the schemes of the site.
* `AlgebraicGeometry.Space.picardProjection_isFiberedInGroupoids`: **condition (1) of
  Stacks 02ZI for the functor of Stacks 04WN**, the projection of `Picardstack_{X/B}` to the
  schemes of the big fppf site is fibred in groupoids.

## Implementation notes

**The category of Section 0372 is taken as a hypothesis, as it is where it is introduced.**
Section 0372 names `Picardstack_{X/B}` a category by designation and verifies nothing, so
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean` records the category structure together
with its projection and the identification of its hom-sets, identities, composition and
projection as the *specification* `AlgebraicGeometry.Space.PicardCategoryData`, and constructs
no value of it.  A statement about the functor `p` of Stacks 04WN is therefore a statement about
`AlgebraicGeometry.Space.PicardCategoryData.projection`, for a value of that specification
supplied as a hypothesis, over the coherence data
`AlgebraicGeometry.Space.ModulePushforwardCoherence` of Stacks 03LU that the identities and the
composition of `Picardstack_{X/B}` already need.  Because the specification pins the hom-sets,
identities, composition and projection, this is a statement about the functor of the source and
not about some other functor on the same objects.

**Invertibility of an inverse image is not a hypothesis.**  The lifting half needs the inverse
image of an invertible module along `X_h : X_V ⟶ X_U` to be invertible, without which there is
no pullback object at all; that is `AlgebraicGeometry.Space.modulePullbackInvertible` of
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean`, and the statements below supply it
rather than assume it.

**What of Stacks 04WN is here, and what is not.**  Stacks 04WN is the conjunction of the three
conditions of Stacks 02ZI (`CategoryTheory.Functor.IsStackInGroupoids`) for `p`.  Condition (1),
that `p` is fibred in groupoids, is proved below.  Conditions (2) and (3) — that the `Isom`
presheaves are sheaves, and that descent data are effective — are *not* proved, and the source's
proof of them is a single citation: after the base maps `b_i` have been glued and the covering
`{U_i ⟶ U}` has been base-changed to the covering `{X_i ⟶ X_U}`, the descent datum for the
invertible modules is effective by Descent on Spaces, Proposition 74.4.1 (Stacks 04W8).  That
proposition is not available in this development: fpqc descent of quasi-coherent modules is
carried here only for *schemes*
(`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor'` and
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`), and
`StacksFrontier/AlgebraicGeometry/Quot/PicardFunctor.lean` records that the corresponding statement
for the small étale site of an algebraic space cannot even be stated here, there being no sheaf
of units and no group of global units of the structure sheaf of an algebraic space.  The
attribute below is qualified accordingly, and no unqualified 04WN claim is made.

**The "up to a replacement as in Remark 03ZZ" clause of the source.**  That clause is a size
reduction: in the source the objects of `Picardstack_{X/B}` form a proper class, so `p` cannot be
a stack on the nose and is replaced by its restriction to a full subcategory with set-sized
fibres.  In Lean the clause is empty *for the purpose of stating the tag*:
`AlgebraicGeometry.Space.PicardObject` is a type, `AlgebraicGeometry.Space.PicardCategoryData`
gives it a genuine `CategoryTheory.Category` instance, and the predicates of Stacks 02ZI and
Stacks 026F are predicates on a functor between categories, so they apply to `p` directly with
no replacement.  The source's replacement is itself available when it is wanted: it is
`CategoryTheory.Functor.IsStack.fibreRepresentatives` and
`CategoryTheory.Functor.isEquivalence_ι_fibreRepresentatives` of
`StacksFrontier/CategoryTheory/Sites/Stack/FibreRepresentatives.lean`, which cut any `p` whose
fibres are essentially small down to a full subcategory whose objects form a set, carry the
conditions of Stacks 026F along, and have fully faithful and essentially surjective inclusion.
Applying them to the projection below is a one-line instantiation once the stack condition is
in hand; nothing of the clause is dropped, and nothing of it is needed to state what is proved.

**The statement of the source is over the schemes of the site, and so is the one below.**  The
functor `p` of Stacks 04WN lands in `(Sch/S)_fppf`, whereas
`AlgebraicGeometry.Space.PicardCategoryData.projection` lands in the test schemes over the base,
which are the costructured arrows `AlgebraicGeometry.Space.PicardSituation.SchemesOver`.  The
two are related by `CategoryTheory.CostructuredArrow.proj`, which is fibred in groupoids for any
functor and any object by
`CategoryTheory.Functor.IsFiberedInGroupoids.costructuredArrow_proj`, so Stacks 09WW composes
the relative statement into the one of the source.  The relative statement is the stronger of
the two and is the one carrying the content.

**On importing `StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean`.**  The calculus
that undoes a composition of fibre morphisms —
`CategoryTheory.Functor.fibreCompLeftInv` and its three laws — is stated there, in the file
whose own implementation notes record that it "belongs in a file of its own"; this is its second
consumer, which is the case for extracting it.  Its right home is beside
`CategoryTheory.Functor.fibreComp` in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStack.lean`, which
`StacksFrontier/AlgebraicGeometry/Quot/PicardStack.lean` already imports for the same reason.
`CategoryTheory.eqToHom_self_comp`, which the two fill-in proofs below use to discharge the
transport along an equality of base maps, is taken from there too: this file carried its own
copy of that one-line lemma under the name `eqToHom_self_comp_picard` until the two were
merged.

The module universe is the universe of the structure rings, as it is for
`AlgebraicGeometry.Space.modulePullback` and for `AlgebraicGeometry.Space.PicardObject`; there is
no second module universe to be polymorphic in.

## References

* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09WW](https://stacks.math.columbia.edu/tag/09WW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The pullback of an object along a morphism of test schemes -/

namespace PicardSituation

variable {s : PicardSituation B S hS}

/-- The pullback of an object of `Picardstack_{X/B}` along a morphism `h : V ⟶ U` of test
schemes over the base: the test scheme `V`, with the inverse image of the invertible module
along the induced morphism `X_h : X_V ⟶ X_U` of base changes.

That the inverse image is again invertible is
`AlgebraicGeometry.Space.modulePullbackInvertible`. -/
def pullbackObject (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    PicardObject s where
  T := V
  lineBundle := (modulePullback B S hS (baseChangeMap s.f h)).obj A.lineBundle
  invertible := modulePullbackInvertible (baseChangeMap s.f h) A.lineBundle A.invertible

@[simp]
theorem pullbackObject_T (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    (pullbackObject A h).T = V :=
  rfl

@[simp]
theorem pullbackObject_lineBundle (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    (pullbackObject A h).lineBundle =
      (modulePullback B S hS (baseChangeMap s.f h)).obj A.lineBundle :=
  rfl

/-- The morphism of `Picardstack_{X/B}` from the pullback of an object to that object: the given
morphism of test schemes, with the identity as its comparison of modules. -/
def pullbackHom (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    PicardHom (pullbackObject A h) A where
  base := h
  fibre := 𝟙 ((modulePullback B S hS (baseChangeMap s.f h)).obj A.lineBundle)
  isIso_fibre := IsIso.id _

@[simp]
theorem pullbackHom_base (A : PicardObject s) {V : s.SchemesOver} (h : V ⟶ A.T) :
    (pullbackHom A h).base = h :=
  rfl

end PicardSituation

/-! ### The calculus of morphisms of `Picardstack_{X/B}` the fill-in needs -/

namespace PicardHom

variable {s : PicardSituation B S hS} {A C D : PicardObject s}

/-- Two equal morphisms of `Picardstack_{X/B}` have the same comparison of modules,
heterogeneously: the type of the comparison depends on the base map, so this is the form in
which the comparison of modules may be projected out of an equality of morphisms. -/
private theorem heq_fibre {m n : PicardHom A C} (e : m = n) : HEq m.fibre n.fibre := by
  subst e
  rfl

/-- Morphisms with the same base map and the same comparison of modules are equal. -/
private theorem mk_eq_mk_of_fibre_eq {b : A.T ⟶ C.T} {f g} (h : f = g) {i j} :
    (⟨b, f, i⟩ : PicardHom A C) = ⟨b, g, j⟩ := by
  subst h
  rfl

/-- **Composition with a fixed morphism on the right is injective on the morphisms with a given
base map.**  The comparison of modules of the right factor is invertible, so the comparison of
modules of the composite determines the one of the left factor. -/
theorem comp_cancel_right (Φ : PicardHom C D) {m n : PicardHom A C}
    (hb : m.base = n.base) (e : m.comp Φ = n.comp Φ) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  have h : Functor.fibreComp (baseChangeCompComparison s.f mb Φ.base) mf Φ.fibre =
      Functor.fibreComp (baseChangeCompComparison s.f mb Φ.base) nf Φ.fibre :=
    by
    have h0 : (PicardHom.comp (⟨mb, mf, mi⟩ : PicardHom A C) Φ).fibre =
        (PicardHom.comp (⟨mb, nf, ni⟩ : PicardHom A C) Φ).fibre :=
      eq_of_heq (heq_fibre e)
    dsimp only [PicardHom.comp] at h0
    exact h0
  exact mk_eq_mk_of_fibre_eq
    (Functor.fibreComp_left_injective (baseChangeCompComparison s.f mb Φ.base) Φ.fibre h)

end PicardHom

/-! ### The fill-in -/

namespace PicardSituation

variable {s : PicardSituation B S hS} {x y z : PicardObject s}

/-- **The fill-in of the proof of Stacks 04WN.**  Let `Φ : y ⟶ x` be a morphism of
`Picardstack_{X/B}`, let `β : z.T ⟶ y.T` be a morphism of test schemes over the base, and let
`c` be an invertible comparison of the inverse image of the module of `x` along
`X_{β ≫ Φ.base}` with the module of `z` — that is, the comparison of a morphism `z ⟶ x` whose
base map factors as `β ≫ Φ.base`.  The fill-in `z ⟶ y` is `β` together with the composite

`(X_β)^*L_y ⟶ (X_β)^*(X_{Φ.base})^*L_x = (X_{β ≫ Φ.base})^*L_x ⟶ L_z`

of the inverse image of the inverse of the comparison of `Φ`, the inverse of the comparison of
Stacks 03LU for the composite, and `c`.

The factorisation of the base map is taken as the *shape* of `c` rather than as a separate
equation, which is what keeps every transport out of this definition: a
`CategoryTheory.eqToHom` along an equality of base maps makes the kernel's check of the
definition diverge, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`.  A consumer
holding the equation instead substitutes it into the morphism it is factoring. -/
def fillIn (Φ : PicardHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (baseChangeMap s.f (β ≫ Φ.base))).obj x.lineBundle ⟶
      z.lineBundle) [IsIso c] : PicardHom z y where
  base := β
  fibre := Functor.fibreCompLeftInv (baseChangeCompComparison s.f β Φ.base) Φ.fibre c
  isIso_fibre := inferInstance

@[simp]
theorem fillIn_base (Φ : PicardHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (baseChangeMap s.f (β ≫ Φ.base))).obj x.lineBundle ⟶
      z.lineBundle) [IsIso c] : (fillIn Φ β c).base = β :=
  rfl

/-- **The fill-in does factor the given morphism.** -/
theorem fillIn_comp (Φ : PicardHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (baseChangeMap s.f (β ≫ Φ.base))).obj x.lineBundle ⟶
      z.lineBundle) (hc : IsIso c) :
    (fillIn Φ β c).comp Φ = ⟨β ≫ Φ.base, c, hc⟩ := by
  exact PicardHom.mk_eq_mk_of_fibre_eq
    (Functor.fibreComp_fibreCompLeftInv (baseChangeCompComparison s.f β Φ.base) Φ.fibre c)

/-- **The fill-in is the only one.**  A morphism of `Picardstack_{X/B}` with the given base map
which factors the given morphism is the fill-in. -/
theorem eq_fillIn (Φ : PicardHom y x) (β : z.T ⟶ y.T)
    (c : (modulePullback B S hS (baseChangeMap s.f (β ≫ Φ.base))).obj x.lineBundle ⟶
      z.lineBundle) (hc : IsIso c) {m : PicardHom z y} (hb : m.base = β)
    (hcomp : m.comp Φ = ⟨β ≫ Φ.base, c, hc⟩) : m = fillIn Φ β c :=
  PicardHom.comp_cancel_right Φ hb (hcomp.trans (fillIn_comp Φ β c hc).symm)

end PicardSituation

/-! ### The projection to the test schemes over the base -/

/-- **The projection of `Picardstack_{X/B}` to the test schemes over the base is fibred in
groupoids.**

This is the content of condition (1) of Stacks 02ZI for the functor of Stacks 04WN, relative to
the base: the lift of a morphism of test schemes over the base at an object is the pullback
`AlgebraicGeometry.Space.PicardSituation.pullbackObject` of that object with the morphism
`AlgebraicGeometry.Space.PicardSituation.pullbackHom`, and the fill-in is
`AlgebraicGeometry.Space.PicardSituation.fillIn`, unique by
`AlgebraicGeometry.Space.PicardSituation.eq_fillIn`.

The category structure on the objects, its projection, and the identification of both with the
ones of Section 0372 are the hypothesis `cd`, and the coherences of Stacks 03LU for the inverse
images are `hc`, which `cd` already needs.  The invertibility of an inverse image, which the
lifting half uses, is proved and not assumed.  See the implementation notes of the file. -/
theorem picardProjection_isFiberedInGroupoids_schemesOver
    (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (cd : PicardCategoryData hc s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    cd.projection.IsFiberedInGroupoids := by
  let _ : Category.{u + 1} (PicardObject s) := cd.category
  have key : ∀ {A C : PicardObject s} (m : A ⟶ C),
      ((Equiv.cast (cd.hom_type A C)) m).base =
        eqToHom (cd.projection_obj A).symm ≫ cd.projection.map m ≫
          eqToHom (cd.projection_obj C) := by
    intro A C m
    rw [cd.projection_map m]
    simp
  constructor
  · intro V U f x hx
    refine ⟨PicardSituation.pullbackObject x
        (f ≫ eqToHom (hx.symm.trans (cd.projection_obj x))),
      (Equiv.cast (cd.hom_type _ _)).symm (PicardSituation.pullbackHom x
        (f ≫ eqToHom (hx.symm.trans (cd.projection_obj x)))),
      IsHomLift.of_fac' cd.projection f _ (cd.projection_obj _) hx ?_⟩
    rw [cd.projection_map, Equiv.apply_symm_apply, PicardSituation.pullbackHom_base]
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
    refine ⟨(Equiv.cast (cd.hom_type z y)).symm (PicardSituation.fillIn Φ β Ψf), ⟨?_, ?_⟩, ?_⟩
    · rw [cd.projection_map, Equiv.apply_symm_apply, PicardSituation.fillIn_base, ← hβ]
      simp
    · refine (Equiv.cast (cd.hom_type z x)).injective ?_
      rw [cd.composition, Equiv.apply_symm_apply, hΦ, hΨ]
      exact PicardSituation.fillIn_comp Φ β Ψf Ψi
    · intro χ hχ
      refine (Equiv.cast (cd.hom_type z y)).injective ?_
      rw [Equiv.apply_symm_apply]
      refine PicardSituation.eq_fillIn Φ β Ψf Ψi ?_ ?_
      · rw [key χ, hχ.1, hβ]
      · have h₂ := cd.composition χ φ
        rw [hχ.2, hΦ, hΨ] at h₂
        exact h₂.symm

/-! ### Condition (1) of Stacks 02ZI for the functor of Stacks 04WN -/

/-- **Condition (1) of Stacks 02ZI for the functor of Stacks 04WN.**  In Situation 0D25 the
projection `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` of Section 0372, which sends an object
`(U, b, L)` to its test scheme `U`, is fibred in groupoids.

The projection of `Picardstack_{X/B}` to the test schemes over the base is fibred in groupoids
by `AlgebraicGeometry.Space.picardProjection_isFiberedInGroupoids_schemesOver`, the projection
of the test schemes over the base to the schemes of the site is fibred in groupoids by
`CategoryTheory.Functor.IsFiberedInGroupoids.costructuredArrow_proj`, and Stacks 09WW composes
the two.

**This carrier asserts the first of the three conditions of Stacks 02ZI, and asserts it
conditionally.**  Stacks 04WN is the conjunction of all three for this functor, and conditions
(2) and (3) — the `Isom` presheaves being sheaves, and effectivity of descent data — are not
proved here: the source proves them by citing Descent on Spaces, Proposition 74.4.1
(Stacks 04W8), fpqc descent of quasi-coherent modules on algebraic spaces, which this
development does not carry.  Of the hypotheses, `cd` is the category of Section 0372, which the
source introduces by designation, and `hc` is the pseudofunctoriality of Stacks 03LU that its
identities and composition already need.
The attribute is qualified accordingly, and no unqualified 04WN claim is made here.  The
source's "up to a replacement as in Remark 03ZZ" clause needs nothing: see the implementation
notes of the file. -/
@[stacks 04WN "condition (1) of Stacks 02ZI only — the functor Picardstack_{X/B} ⟶ \
(Sch/S)_fppf is fibred in groupoids — and conditional on the category of Section 0372; \
conditions (2) and (3) need Stacks 04W8, which this development does not carry"]
theorem picardProjection_isFiberedInGroupoids (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} (cd : PicardCategoryData hc s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    Functor.IsFiberedInGroupoids
      (cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base) :=
  let : Category.{u + 1} (PicardObject s) := cd.category
  Functor.IsFiberedInGroupoids.comp cd.projection
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
    (picardProjection_isFiberedInGroupoids_schemesOver hc cd)
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj (schemeSpaceFunctor B S hS) s.base)

end AlgebraicGeometry.Space

end
