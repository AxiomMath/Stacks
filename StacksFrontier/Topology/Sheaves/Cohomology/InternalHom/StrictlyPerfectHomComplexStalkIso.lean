module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomComplexStalkProduct

/-!
# The stalk of the internal Hom complex is the Hom complex of the stalks

Let `Rc` be a sheaf of commutative rings on a topological space `X`, write `O_X` for the
underlying sheaf of rings, let `E` and `F` be complexes of `O_X`-modules and let `x ∈ X`. Two
comparisons between the stalk at `x` of the internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z and the naive Hom complex of the complexes of stalks are already available:

* degreewise, `Stacks.SheafOfModules.sheafHomComplexStalkDegreeEquiv`, built from the
  direct-sum description of Stacks 08DM and Stacks 01CP at each term;
* as a morphism of complexes, `Stacks.SheafOfModules.sheafHomComplexStalkChainMap`, built from
  `SheafHomComplex.sectionsIso` and the differential assembly `cochainStalk_δ`, with no
  hypothesis at all.

They are built along different routes. This file shows that they **agree**, and concludes that
the comparison of complexes is an isomorphism for `E` bounded with every term a direct summand
of a finite free module.

The agreement is `Stacks.SheafOfModules.homComplexStalkCochainMap_v`: the `(-q, n-q)` component
of the degree-`n` comparison is the image, under the Stacks 01CP identification at the `q`-th
term, of the stalk map of the `q`-th degree projection
`AlgebraicGeometry.RingedSite.homDegreeProjection X E F n q`. Those projections and that
identification are exactly the two ingredients of `sheafHomComplexStalkDegreeEquiv`, so this
says the two comparisons are computed by the same data.

## Main results

* `Stacks.SheafOfModules.internalHomSheafStalkEquiv_germ_eq_stalkLinearMap`: **Stacks 01CP is
  taking stalks of a local homomorphism.** The identification carries the germ of a section of
  the internal Hom sheaf to the stalk map of the homomorphism that section names. This is the
  bundled form of `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkMap_germ`.
* `Stacks.SheafOfModules.homComplexStalkCochainMap_v` and
  `Stacks.SheafOfModules.sheafHomComplexStalkDegreeEquiv_apply`: **the agreement.** The first
  computes the `(-q, n-q)` component of the comparison of complexes, the second the `q`-th
  component of the degreewise equivalence, and the two answers are the same.
* `Stacks.SheafOfModules.bijective_homComplexStalkCochainMap`: the degree-`n` comparison is
  bijective, for `E` bounded with every term a finite free summand. Injectivity is joint
  injectivity of the stalk maps of the degree projections
  (`modStalkMap_homDegreeProjection_jointly_injective`, i.e. the product half of the
  stalk/limit interchange) together with injectivity of Stacks 01CP at each term; surjectivity
  is the surjectivity of the product half, which is where boundedness of `E` is used.
* `Stacks.SheafOfModules.homComplexStalkCochainMap_v_canonical`,
  `Stacks.SheafOfModules.bijective_homComplexStalkCochainMap_of_bijective` and
  `Stacks.SheafOfModules.isIso_sheafHomComplexStalkChainMap_of_bijective`: **the germ-local
  forms.** The agreement holds at the *canonical* map of Stacks 01CP with no hypothesis
  whatsoever, and bijectivity of the comparison — degreewise and as a map of complexes — follows
  from invertibility of that canonical map at each pair of terms, which is a condition on the
  single stalk at `x`. Combined with
  `Stacks.SheafOfModules.SheafHomStalk.bijective_sheafHomStalkLinearMap_of_localPresentation`
  this is what lets the stalk of `SheafHom(E, F)` be computed when `E` is strictly perfect only
  on a neighbourhood of `x`. The three statements below with a termwise
  `RingedSite.IsFiniteFreeSummand` hypothesis are derived from these.
* `Stacks.SheafOfModules.isIso_sheafHomComplexStalkChainMap`: **the complex-level
  identification is an isomorphism.** For `E` bounded with every term a direct summand of a
  finite free `O_X`-module and `F` arbitrary, `sheafHomComplexStalkChainMap` is an isomorphism
  of complexes
  `SheafHom(E, F)_x ≅ Hom^•_{O_{X,x}}(E_x, F_x)`.

## Implementation notes

The reindexing of `CochainComplex.HomComplex.Triplet n` by a single integer `q ↦ (-q, n - q)`,
which is how the degree projections are indexed, enters only through
`Stacks.SheafOfModules.SheafHomStalk.cochain_ext_neg`: two cochains agreeing on every triplet of
the form `(-q, n - q)` are equal, because every triplet is of that form with `q = -p`. This
keeps the index juggling in one place and out of the statements.

Nothing here unfolds `AlgebraicGeometry.RingedSite.strictlyPerfectHomDegreeIso`, which is
`public` but not `@[expose]`; the degree projections are computed with
`AlgebraicGeometry.RingedSite.homDegreeProjection_val_app_apply` and the product half of the
stalk/limit interchange.

The hypotheses are those of the two sources and no more: `hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite`
(boundedness of `E`, needed for the product half) and
`hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i)` (needed for Stacks 01CP at
each term). There is no hypothesis on `F`.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry DirectSum CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules.SheafHomStalk

/-! ### Cochains indexed by one integer -/

section CochainIndex

variable {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {n : ℤ}

/-- Two degree-`n` cochains that agree on every triplet of the form `(-q, n - q)` are equal:
every triplet `(p, q, p + n = q)` is of that form, with `q = -p`. This is the reindexing of
`CochainComplex.HomComplex.Triplet n` by a single integer, in the form in which it is used. -/
lemma cochain_ext_neg {z z' : Cochain K L n}
    (h : ∀ q : ℤ, z.v (-q) (n - q) (by omega) = z'.v (-q) (n - q) (by omega)) : z = z' := by
  funext T
  obtain ⟨p, q, hpq⟩ := T
  have hT : (⟨p, q, hpq⟩ : Triplet n) = ⟨-(-p), n - -p, by omega⟩ := by
    congr 1 <;> omega
  rw [hT]
  exact h (-p)

end CochainIndex

end Stacks.SheafOfModules.SheafHomStalk

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.SheafHomStalk

/-! ### Stacks 01CP as taking stalks of a local homomorphism -/

section Bridge

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  (A B : SheafOfModules.{u} (structureSheaf Rc))

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- The identification of sections of `internalHomSheafHom` undoes taking the underlying natural
family: the section of the internal Hom sheaf named by a morphism `φ : A|_U ⟶ B|_U` names `φ`
back. -/
lemma internalHomSheafHom_sectionsEquiv_val {U : Opens X} (φ : A.over U ⟶ B.over U) :
    (internalHomSheafHom Rc A B).sectionsEquiv U φ.val = φ := rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Stacks 01CP is taking stalks of a local homomorphism.** The identification of the stalk of
`Hom_{O_X}(A, B)` with the module of `O_{X,x}`-linear maps `A_x →ₗ B_x` carries the germ at `x`
of a section `s` over `U` to the stalk map of the homomorphism `A|_U ⟶ B|_U` that `s` names.

This is the bundled form of `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkMap_germ`: the
underlying map of the equivalence is the canonical map by
`SheafHomStalk.SheafHomStalkLinearEquiv.toLinearMap_eq`, and the canonical map is defined as the
colimit descent of exactly that germ formula. Hypothesis: `A` of finite presentation, as for the
equivalence itself. -/
lemma internalHomSheafStalkEquiv_germ_eq_stalkLinearMap [A.IsFinitePresentation] (x : X)
    (U : Opens X) (hxU : x ∈ U)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) A B).val.obj (op U)) :
    internalHomSheafStalkEquiv Rc A B x
        (germAt (RingedSite.internalHomSheaf (ringedSite Rc) A B) U x hxU s)
      = stalkLinearMap ((internalHomSheafHom Rc A B).sectionsEquiv U s) hxU := by
  have hcoe := SheafHomStalkLinearEquiv.toLinearMap_eq
    (sheafHomStalkLinearEquivOfFinitePresentation (internalHomSheafHom Rc A B) x)
  have h1 : internalHomSheafStalkEquiv Rc A B x
      (germAt (RingedSite.internalHomSheaf (ringedSite Rc) A B) U x hxU s)
      = sheafHomStalkLinearMap (internalHomSheafHom Rc A B) x
        (germAt (RingedSite.internalHomSheaf (ringedSite Rc) A B) U x hxU s) :=
    LinearMap.congr_fun hcoe _
  rw [h1]
  exact sheafHomStalkMap_germ (internalHomSheafHom Rc A B) U hxU s

/-- **Stacks 01CP at a finite free summand is taking stalks of a local homomorphism.** The germ
formula `internalHomSheafStalkEquiv_germ_eq_stalkLinearMap`, with the finite-presentation
hypothesis supplied by the finite-free-summand hypothesis on `A`. -/
lemma internalHomSheafStalkEquivOfIsFiniteFreeSummand_germ
    (hA : RingedSite.IsFiniteFreeSummand (ringedSite Rc) A) (x : X)
    (U : Opens X) (hxU : x ∈ U)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) A B).val.obj (op U)) :
    internalHomSheafStalkEquivOfIsFiniteFreeSummand Rc A B hA x
        (germAt (RingedSite.internalHomSheaf (ringedSite Rc) A B) U x hxU s)
      = stalkLinearMap ((internalHomSheafHom Rc A B).sectionsEquiv U s) hxU := by
  let : A.IsFinitePresentation := hA.isFinitePresentation (ringedSite Rc)
  exact internalHomSheafStalkEquiv_germ_eq_stalkLinearMap Rc A B x U hxU s

end Bridge

/-! ### The agreement, and the complex-level isomorphism -/

section Agreement

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)
  (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
  (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i))
  (n : ℤ) (x : X)

omit hE [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- **The agreement of the two comparisons, at the canonical map of Stacks 01CP.** The
`(-q, n-q)` component of the degree-`n` comparison `homComplexStalkCochainMap` is the image,
under the *canonical* map `Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkLinearMap` of
Stacks 01CP at the `q`-th term, of the stalk map of the `q`-th degree projection.

**There is no hypothesis at all**: the canonical map exists for any source, and the germ formula
`Stacks.SheafOfModules.SheafHomStalk.sheafHomStalkMap_germ` that pins it down needs no finiteness.
`homComplexStalkCochainMap_v` is this statement read through the Stacks 01CP *equivalence*, which
is where a finiteness hypothesis is needed — only to know that the canonical map is invertible,
never to compute it. -/
lemma homComplexStalkCochainMap_v_canonical (q : ℤ)
    (t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x) :
    (homComplexStalkCochainMap
          (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) n x t).v
        (-q) (n - q) (by omega)
      = ModuleCat.ofHom (sheafHomStalkLinearMap
          (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x
          (modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t)) := by
  obtain ⟨U, hxU, s, rfl⟩ := exists_germ_eq
    ((ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)).obj.X n) t
  have hL := congrArg (fun z : Cochain (modStalkComplex E x) (modStalkComplex F x) n =>
      z.v (-q) (n - q) (by omega))
    (homComplexStalkCochainMap_germ
      (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) n x U hxU s)
  have hR := congrArg (fun y => ModuleCat.ofHom
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x y))
    (modStalkMap_germ (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x U hxU s)
  have hB := congrArg ModuleCat.ofHom
    (sheafHomStalkMap_germ (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) U hxU
      ((RingedSite.homDegreeProjection (ringedSite Rc) E F n q).val.app (op U) s))
  exact hL.trans (hB.symm.trans hR.symm)

omit hE in
/-- **The agreement of the two comparisons.** The `(-q, n-q)` component of the degree-`n`
comparison `homComplexStalkCochainMap` is the image, under the Stacks 01CP identification at the
`q`-th term, of the stalk map of the `q`-th degree projection
`AlgebraicGeometry.RingedSite.homDegreeProjection X E F n q`.

Those projections and that identification are the two ingredients of
`sheafHomComplexStalkDegreeEquiv`, so this is the statement that the comparison of complexes and
the degreewise equivalence are computed by the same data.

The only hypothesis is `hterm` at the single index `-q`, needed to name the Stacks 01CP
identification there; `E` need not be bounded and `F` is arbitrary. -/
lemma homComplexStalkCochainMap_v (q : ℤ)
    (t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x) :
    (homComplexStalkCochainMap
          (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) n x t).v
        (-q) (n - q) (by omega)
      = ModuleCat.ofHom (internalHomSheafStalkEquivOfIsFiniteFreeSummand Rc
          (E.X (-q)) (F.X (n - q)) (hterm (-q)) x
          (modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t)) := by
  -- The Stacks 01CP equivalence *is* the canonical map, by `sheafHomStalkLinearMap_unique`.
  let : (E.X (-q)).IsFinitePresentation :=
    (hterm (-q)).isFinitePresentation (ringedSite Rc)
  have heq := SheafHomStalkLinearEquiv.toLinearMap_eq
    (sheafHomStalkLinearEquivOfFinitePresentation
      (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x)
  rw [homComplexStalkCochainMap_v_canonical Rc E F n x q t]
  exact congrArg ModuleCat.ofHom (LinearMap.congr_fun heq.symm _)

/-- **The degreewise equivalence, componentwise.** The `q`-th component of the direct-sum
description `sheafHomComplexStalkDegreeEquiv` of the stalk of the degree-`n` term is the
Stacks 01CP identification at the `q`-th term applied to the stalk map of the `q`-th degree
projection.

Together with `homComplexStalkCochainMap_v`, which says the same of the `(-q, n-q)` component
of the comparison of complexes, this is the agreement of the two comparisons: each is the family
of stalk maps of the degree projections, read through Stacks 01CP at each term.

The hypotheses are those of `sheafHomComplexStalkDegreeEquiv` itself: `E` bounded and every term
of `E` a direct summand of a finite free module. -/
theorem sheafHomComplexStalkDegreeEquiv_apply (q : ℤ)
    (t : modStalk ((RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n) x) :
    sheafHomComplexStalkDegreeEquiv Rc E F hE hterm n x t q
      = internalHomSheafStalkEquivOfIsFiniteFreeSummand Rc (E.X (-q)) (F.X (n - q))
          (hterm (-q)) x
          (modStalkMap (RingedSite.homDegreeProjection (ringedSite Rc) E F n q) x t) := by
  have h := modStalkMap_homDegreeProjection_sheafHomDegreeStalkCoprodEquiv Rc E F hE n x q
    ((sheafHomDegreeStalkCoprodEquiv Rc E F hE n x).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact congrArg (internalHomSheafStalkEquivOfIsFiniteFreeSummand Rc (E.X (-q)) (F.X (n - q))
    (hterm (-q)) x) h.symm

include hE in
omit [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- **The degree-`n` comparison is bijective, from invertibility of Stacks 01CP at each pair of
terms.** For `E` bounded and `F` arbitrary, the comparison from the stalk at `x` of the degree-`n`
term of `SheafHom(E, F)` to the degree-`n` term of the naive Hom complex of the complexes of
stalks is bijective as soon as the canonical map of Stacks 01CP is bijective at each pair
`(E.X i, F.X j)`.

This is the form that applies when `E` is strictly perfect only *near* `x`: the hypothesis is
about the stalk at the single point `x`, and
`Stacks.SheafOfModules.SheafHomStalk.bijective_sheafHomStalkLinearMap_of_localPresentation`
supplies it from a local presentation of `E.X i` at `x`, with no hypothesis on `E` away from a
neighbourhood of `x`. `bijective_homComplexStalkCochainMap` is the global-hypothesis form.

Injectivity is joint injectivity of the stalk maps of the degree projections — the product half
of the stalk/limit interchange, `modStalkMap_homDegreeProjection_jointly_injective` — together
with injectivity of Stacks 01CP at each term. Surjectivity is surjectivity of the product half:
a cochain of maps of stalks is read, term by term, as a family of germs of the internal Hom
sheaves, and the product half produces the germ of the degree-`n` term with those components. -/
theorem bijective_homComplexStalkCochainMap_of_bijective
    (h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x)) :
    Function.Bijective (homComplexStalkCochainMap
      (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) n x) := by
  classical
  let e (q : ℤ) := LinearEquiv.ofBijective
    (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x)
    (h01 (-q) (n - q))
  constructor
  · intro t t' htt'
    refine modStalkMap_homDegreeProjection_jointly_injective Rc E F hE n x fun q => ?_
    have h := congrArg (fun z : Cochain (modStalkComplex E x) (modStalkComplex F x) n =>
      z.v (-q) (n - q) (by omega)) htt'
    have h2 := homComplexStalkCochainMap_v_canonical Rc E F n x q t
    have h3 := homComplexStalkCochainMap_v_canonical Rc E F n x q t'
    exact (e q).injective
      (congrArg ModuleCat.Hom.hom (h2.symm.trans (h.trans h3)))
  · intro z
    refine ⟨(sheafHomDegreeStalkProdEquiv Rc E F hE n x).symm (fun q : ℤ =>
      (e q).symm (ModuleCat.Hom.hom (z.v (-q) (n - q) (by omega)))), ?_⟩
    refine cochain_ext_neg fun q => ?_
    -- The product half reads the chosen germ off at `q` as the `q`-th member of the family, and
    -- Stacks 01CP at the `q`-th term then undoes the choice of preimage.  Both steps are taken
    -- as equations rather than by `rw`: the internal Hom sheaf named through `internalHomSheafHom`
    -- is not type-correct at `implicit` transparency, so no motive can be built in this goal.
    refine (homComplexStalkCochainMap_v_canonical Rc E F n x q _).trans ?_
    refine (congrArg (fun y => ModuleCat.ofHom
        (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X (-q)) (F.X (n - q))) x y))
      (((sheafHomDegreeStalkProdEquiv_apply Rc E F hE n x _ q).symm).trans
        (congrFun ((sheafHomDegreeStalkProdEquiv Rc E F hE n x).apply_symm_apply _) q))).trans ?_
    exact congrArg ModuleCat.ofHom ((e q).apply_symm_apply _)

/-- Stacks 01CP is invertible at a pair of terms when the source is a finite free summand. -/
private lemma bijective_sheafHomStalkLinearMap_of_isFiniteFreeSummand (i j : ℤ)
    (hi : RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i)) :
    Function.Bijective (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x) := by
  let : (E.X i).IsFinitePresentation := hi.isFinitePresentation (ringedSite Rc)
  exact ⟨injective_sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x,
    surjective_sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x⟩

include hE hterm in
/-- **The degree-`n` comparison is bijective.** For `E` bounded with every term a direct summand
of a finite free `O_X`-module, and `F` arbitrary, the comparison from the stalk at `x` of the
degree-`n` term of `SheafHom(E, F)` to the degree-`n` term of the naive Hom complex of the
complexes of stalks is bijective.

This is `bijective_homComplexStalkCochainMap_of_bijective`, whose hypothesis is invertibility of
Stacks 01CP at each pair of terms, applied to the two halves of Stacks 01CP at a source of finite
presentation. -/
theorem bijective_homComplexStalkCochainMap :
    Function.Bijective (homComplexStalkCochainMap
      (ofSite Rc E F (RingedSite.sheafHomComplex (ringedSite Rc) E F)) n x) :=
  bijective_homComplexStalkCochainMap_of_bijective Rc E F hE n x
    (fun i j => bijective_sheafHomStalkLinearMap_of_isFiniteFreeSummand Rc E F x i j (hterm i))

include hE in
omit [∀ T : Opens X, HasSheafify ((Opens.grothendieckTopology X).over T) AddCommGrpCat.{u}]
  [∀ T : Opens X, ((Opens.grothendieckTopology X).over T).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- **The complex-level identification is an isomorphism, from invertibility of Stacks 01CP at
each pair of terms.** For `E` bounded and `F` arbitrary, the comparison of complexes
`sheafHomComplexStalkChainMap` is an isomorphism as soon as the canonical map of Stacks 01CP is
bijective at each pair `(E.X i, F.X j)` — a condition on the single stalk at `x`.

`isIso_sheafHomComplexStalkChainMap` is the global-hypothesis form. -/
theorem isIso_sheafHomComplexStalkChainMap_of_bijective
    (h01 : ∀ i j : ℤ, Function.Bijective
      (sheafHomStalkLinearMap (internalHomSheafHom Rc (E.X i) (F.X j)) x)) :
    IsIso (sheafHomComplexStalkChainMap Rc E F x) := by
  have : ∀ m : ℤ, IsIso ((sheafHomComplexStalkChainMap Rc E F x).f m) := fun m =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_homComplexStalkCochainMap_of_bijective Rc E F hE m x h01)
  exact HomologicalComplex.Hom.isIso_of_components _

include hE hterm in
/-- **The complex-level identification is an isomorphism.** For `E` bounded with every term a
direct summand of a finite free `O_X`-module and `F` arbitrary, the comparison of complexes
`sheafHomComplexStalkChainMap` from the stalk at `x` of the internal Hom complex
`SheafHom(E, F)` of Stacks 0A8Z to the naive Hom complex `Hom^•_{O_{X,x}}(E_x, F_x)` of the
complexes of stalks over the stalk ring is an isomorphism.

Hypotheses: `hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite` and
`hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i)`, i.e. `E` strictly
perfect; nothing on `F`. The comparison itself needs neither — it exists for any `E` and `F` —
so this adds no hypothesis to the statement that it is the canonical map. -/
theorem isIso_sheafHomComplexStalkChainMap :
    IsIso (sheafHomComplexStalkChainMap Rc E F x) :=
  isIso_sheafHomComplexStalkChainMap_of_bijective Rc E F hE x
    (fun i j => bijective_sheafHomStalkLinearMap_of_isFiniteFreeSummand Rc E F x i j (hterm i))

end Agreement

end Stacks.SheafOfModules

end
