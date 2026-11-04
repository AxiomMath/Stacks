module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexOpenNaturality

/-!
# The local description of the internal Hom complex is compatible with restriction

Let `(C, O)` be a ringed site, let `K` and `M` be complexes of `O`-modules and let
`H : SheafHomComplex X K M` be a realization of their internal Hom complex.  Its field
`restrict_natural` says that the identification of the sections of `H.obj` over an object `V`
with the degree-`n` cochains from `K|_V` to `M|_V` commutes with restriction along an arrow
`g : W ⟶ V` — but it says it *pointwise on local sections of `K`*, one component of one cochain
at a time, which is not a form anything can be deduced from without first reassembling it.

This file reassembles it: it constructs the restriction of a cochain along an arrow of the site,
proves that it is additive and commutes with the differential of the Hom complex, and proves that
the local description carries restriction of sections to it, as a single equality of cochains.

## Main definitions

* `AlgebraicGeometry.RingedSite.cochainRestrict`: the restriction along an arrow of the site of
  a cochain between the restrictions of two complexes of `O`-modules.  This is the restriction
  map of the rule `V ↦ Hom^•(K|_V, M|_V)`.
* `AlgebraicGeometry.RingedSite.homComplexRestrict`: the same, packaged as a morphism of cochain
  complexes of abelian groups `Hom^•(K|_V, M|_V) ⟶ Hom^•(K|_W, M|_W)`.

## Main results

* `Stacks.SheafOfModules.overFunctor_eq_comp_overMap`: restricting sheaves of modules to the
  slice over `V` and then along `g : W ⟶ V` is restricting them to the slice over `W`, as an
  equality of functors.
* `Stacks.SheafOfModules.overFunctor_map_overMap`: the same on a morphism of sheaves of modules.
* `AlgebraicGeometry.RingedSite.restrictComplex_X_overMap` and
  `AlgebraicGeometry.RingedSite.restrictComplex_d_overMap`: the same for the terms and the
  differential of a restricted complex.
* `AlgebraicGeometry.RingedSite.cochainRestrict_add` and
  `AlgebraicGeometry.RingedSite.delta_cochainRestrict`: restriction of cochains is additive and
  commutes with the differential `CochainComplex.HomComplex.δ` of the Hom complex.  Together with
  `AlgebraicGeometry.RingedSite.cochainRestrict_zero` these are what
  `AlgebraicGeometry.RingedSite.homComplexRestrict` is built from.
* `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv_restrictSection`: the cochain
  attached to a restricted section is the restriction of the cochain attached to the section.

## Implementation notes

`AlgebraicGeometry.RingedSite.cochainRestrict` is built in the spelling of its target rather than
as `CochainComplex.HomComplex.Cochain.map` along `SheafOfModules.overMap`, and the crossing
between the two spellings is carried explicitly rather than left to the unifier.  Both choices
are forced, by one obstruction with three faces.  The composite `overFunctor V ⋙ overMap g`
**is** `overFunctor W`, and that is `rfl` within the heartbeat budget as an equality of
*functors*, of *objects*, and of *complexes*.  But

* the corresponding equality of `Cochain` **types** is not `rfl` within the budget, because
  `Cochain F G n` is a dependent function type and the unifier descends under the binders of the
  degrees instead of comparing `F` with `F'` and `G` with `G'`.  This is why `Cochain.map` cannot
  be used and `AlgebraicGeometry.RingedSite.cochainRestrict` is defined componentwise: a
  component is a *morphism between objects*, where the comparison is first-order and cheap.
* the corresponding equality of **morphisms**, `(overFunctor W).map f = (overMap g).map
  ((overFunctor V).map f)`, is not `rfl` within the budget either, for the reason analysed in the
  implementation notes of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexOpenNaturality`
  — identifying the ring of sections of a twice-restricted sheaf of rings with the ring of
  sections of the original is expensive.  What *is* cheap is the image of that equality under the
  faithful forgetful functor to presheaves of abelian groups, where both sides are the module's
  action on an arrow of the slice category and `CategoryTheory.Over.map` leaves the source of an
  arrow alone.  That is how `Stacks.SheafOfModules.overFunctor_map_overMap` is proved.
* the corresponding equality at a **sum of morphisms** — one side summed in
  `(overFunctor W).obj A ⟶ (overFunctor W).obj B`, the other in
  `(overMap g).obj ((overFunctor V).obj A) ⟶ (overMap g).obj ((overFunctor V).obj B)` — does not
  yield to descending to local sections at all, since the two additive structures are themselves
  what is being compared.  It is also not needed.  The identification of the two spellings is
  expensive but affordable *once* per declaration, and the whole of this file never spends it
  more than twice in any one proof: it is paid once, at an object, in
  `AlgebraicGeometry.RingedSite.restrictComplex_X_overMap`, whose proof is
  `CategoryTheory.Functor.congr_obj` of the cheap functor-level equality rather than a second
  definitional unfolding; and from then on every step transports along the
  `CategoryTheory.eqToHom` of *that* proof.  The two forms this takes are
  `AlgebraicGeometry.RingedSite.restrictComplex_d_eqToHom`, which is
  `CategoryTheory.Functor.congr_hom` of the same equality, and
  `AlgebraicGeometry.RingedSite.cochainRestrict_v_eqToHom`.  In both, the two sides of the
  equation are composites whose sources and targets are spelled *identically*, so a proof may
  freely add, compose and scale them; `CategoryTheory.eqToHom_trans` collapses each adjacent
  pair, because the composite proof is then an equality of a term with itself.

## What this is for

The naturality in the object of the site of [Stacks, Tag 0A94], which
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOfASolution` needs, is the
commutativity of

```
H^0(Γ(V, SheafHom(K, I)))  ⟶  H^0(Γ(W, SheafHom(K, I)))
          ↓                              ↓
Hom_{D(O|_V)}(K|_V, I|_V)  ⟶  Hom_{D(O|_W)}(K|_W, I|_W)
```

for K-injective `I`, the vertical maps being
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom`.  That square **is
now proved**, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived`, as
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restrict`, and this
file is its chain-level input: `AlgebraicGeometry.RingedSite.homComplexRestrict` above is what
turns `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv_restrictSection` into a square
of morphisms of complexes that can be read on `HomologicalComplex.homologyMap`.

The two steps recorded here as remaining — compatibility with restriction of
`CochainComplex.HomComplex.homologyAddEquiv`, and of
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv` across
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso` — turned out not to be two
squares at all.  The whole identification of Tag 0A94 is a *single* `DerivedCategory.Q.map`, of
the morphism of complexes that a representing degree-zero cocycle names, so the derived-level
square reduces to the chain-level one above together with the naturality of
`CategoryTheory.Functor.mapDerivedCategoryFactors`; see the implementation notes of that file.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Restriction to a slice of the site is transitive, as an equality of functors.**
Restricting sheaves of modules to the slice over `V` and then along `g : W ⟶ V` is restricting
them to the slice over `W`.

Both sides are pushforwards along the same functor and the same morphism of sheaves of rings, so
this is `rfl`, and it is the *one* face of the identification of the two restrictions that is
cheap to check.  Every other face used in this file is derived from it by
`CategoryTheory.Functor.congr_obj` and `CategoryTheory.Functor.congr_hom`, never by a second
definitional unfolding; see the implementation notes. -/
theorem overFunctor_eq_comp_overMap {V W : C} (g : W ⟶ V) :
    SheafOfModules.overFunctor.{w} R W =
      SheafOfModules.overFunctor.{w} R V ⋙ SheafOfModules.overMap.{w} R g :=
  rfl

/-- **Restriction to a slice of the site is transitive on morphisms.** Restricting a morphism of
sheaves of modules to the slice over `V` and then along `g : W ⟶ V` is restricting it to the
slice over `W`.

The two sides are definitionally equal, but not within the heartbeat budget; what is cheap, and
what is checked here, is their image under the faithful forgetful functor to presheaves of
abelian groups.  There both sides are the module's action on an arrow of the slice category over
`W`, and `CategoryTheory.Over.map` leaves the source of an arrow alone. -/
theorem overFunctor_map_overMap {V W : C} (g : W ⟶ V) {A B : SheafOfModules.{w} R} (f : A ⟶ B) :
    (SheafOfModules.overFunctor.{w} R W).map f =
      (SheafOfModules.overMap.{w} R g).map ((SheafOfModules.overFunctor.{w} R V).map f) := by
  ext ⟨T⟩ x
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] additiveOverMap

variable {X : RingedSite.{u, u, u}}
  {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The terms of a restricted complex, in two steps.** The degree-`p` term of `K|_W` is the
restriction along `g : W ⟶ V` of the degree-`p` term of `K|_V`.

This is `Stacks.SheafOfModules.overFunctor_eq_comp_overMap` read at one object, and it is the
only form in which this file uses the identification of the two restrictions on objects: every
later step transports along the `CategoryTheory.eqToHom` of *this* proof instead of asking the
unifier to redo the identification. -/
theorem restrictComplex_X_overMap {V W : X.C} (g : W ⟶ V) (p : ℤ) :
    (restrictComplex X K W).X p =
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).obj
        ((restrictComplex X K V).X p) :=
  Functor.congr_obj (Stacks.SheafOfModules.overFunctor_eq_comp_overMap
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g) (K.X p)

/-- **The differential of a restricted complex, in two steps.** The differential of `K|_W` is the
restriction along `g : W ⟶ V` of the differential of `K|_V`. -/
theorem restrictComplex_d_overMap {V W : X.C} (g : W ⟶ V) (i j : ℤ) :
    (restrictComplex X K W).d i j =
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map
        ((restrictComplex X K V).d i j) :=
  Stacks.SheafOfModules.overFunctor_map_overMap g (K.d i j)

/-- **The differential of a restricted complex, with the identification of the two restrictions
carried explicitly.** The same statement as
`AlgebraicGeometry.RingedSite.restrictComplex_d_overMap`, but with the transport between the two
spellings of the terms of the complex written out as a `CategoryTheory.eqToHom`, so that the two
sides of the equation are composites of morphisms whose sources and targets are spelled
*identically*.  That is what makes it usable in a proof that also has to compare the additive
structures of the two spellings; see the implementation notes. -/
theorem restrictComplex_d_eqToHom {V W : X.C} (g : W ⟶ V) (i j : ℤ) :
    (restrictComplex X K W).d i j =
      eqToHom (restrictComplex_X_overMap g i) ≫
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map
          ((restrictComplex X K V).d i j) ≫
          eqToHom (restrictComplex_X_overMap g j).symm :=
  Functor.congr_hom (Stacks.SheafOfModules.overFunctor_eq_comp_overMap
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) g) (K.d i j)

/-! ### Restriction of cochains between restricted complexes -/

/-- **The restriction of a cochain along an arrow of the site.** A degree-`n` cochain from `K|_V`
to `M|_V` is carried to a degree-`n` cochain from `K|_W` to `M|_W` by restricting each of its
components along `g : W ⟶ V`.

This is the restriction map of the rule `V ↦ Hom^•(K|_V, M|_V)` of [Stacks, Tag 0A8Y].  It is
spelled componentwise rather than as `CochainComplex.HomComplex.Cochain.map` along
`SheafOfModules.overMap`; see the implementation notes for why. -/
def cochainRestrict {V W : X.C} (g : W ⟶ V) {n : ℤ}
    (z : Cochain (restrictComplex X K V) (restrictComplex X M V) n) :
    Cochain (restrictComplex X K W) (restrictComplex X M W) n :=
  Cochain.mk fun p q hpq =>
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map (z.v p q hpq)

/-- The components of a restricted cochain are the restrictions of its components. -/
@[simp]
theorem cochainRestrict_v {V W : X.C} (g : W ⟶ V) {n : ℤ}
    (z : Cochain (restrictComplex X K V) (restrictComplex X M V) n) (p q : ℤ) (hpq : p + n = q) :
    (cochainRestrict g z).v p q hpq =
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map
        (z.v p q hpq) :=
  rfl

/-- **The components of a restricted cochain, with the identification of the two restrictions
carried explicitly.** The same statement as
`AlgebraicGeometry.RingedSite.cochainRestrict_v`, but with the transport between the two
spellings of the terms of the complex written out as a `CategoryTheory.eqToHom`.

This is the form in which the two lemmas below use the definition, and it is what makes them
provable at all: in `AlgebraicGeometry.RingedSite.cochainRestrict_v` the right-hand side is a
morphism `(K|_V)|_g ⟶ (M|_V)|_g` *read as* a morphism `K|_W ⟶ M|_W`, so a proof that also has to
compare a sum formed in the one hom group with a sum formed in the other asks the unifier to
identify the two additive structures, which it does not do within the heartbeat budget.  Here
both sides are composites whose sources and targets are spelled identically, and the whole
identification has been paid for once, in
`AlgebraicGeometry.RingedSite.restrictComplex_X_overMap`. -/
theorem cochainRestrict_v_eqToHom {V W : X.C} (g : W ⟶ V) {n : ℤ}
    (z : Cochain (restrictComplex X K V) (restrictComplex X M V) n) (p q : ℤ)
    (hpq : p + n = q) :
    (cochainRestrict g z).v p q hpq =
      eqToHom (restrictComplex_X_overMap g p) ≫
        (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map
          (z.v p q hpq) ≫
          eqToHom (restrictComplex_X_overMap (K := M) g q).symm :=
  (conj_eqToHom_iff_heq _ _ (restrictComplex_X_overMap g p)
    (restrictComplex_X_overMap (K := M) g q)).mpr HEq.rfl

/-- Restriction carries the zero cochain to the zero cochain. -/
@[simp]
theorem cochainRestrict_zero {V W : X.C} (g : W ⟶ V) (n : ℤ) :
    cochainRestrict (K := K) (M := M) g (0 : Cochain _ _ n) = 0 := by
  apply Cochain.ext
  intro p q hpq
  rw [cochainRestrict_v, Cochain.zero_v, Cochain.zero_v, Functor.map_zero]
  rfl

/-- **Restriction of cochains is additive.** -/
theorem cochainRestrict_add {V W : X.C} (g : W ⟶ V) {n : ℤ}
    (z z' : Cochain (restrictComplex X K V) (restrictComplex X M V) n) :
    cochainRestrict g (z + z') = cochainRestrict g z + cochainRestrict g z' := by
  apply Cochain.ext
  intro p q hpq
  simp only [cochainRestrict_v_eqToHom, Cochain.add_v, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- **Restriction of cochains commutes with the differential of the Hom complex.** Together with
`AlgebraicGeometry.RingedSite.cochainRestrict_add` and
`AlgebraicGeometry.RingedSite.cochainRestrict_zero` this makes restriction along `g : W ⟶ V` a
morphism of cochain complexes of abelian groups `Hom^•(K|_V, M|_V) ⟶ Hom^•(K|_W, M|_W)`, which
is what turns the equality of cochains of
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv_restrictSection` into a square that
can be read on `homologyMap`. -/
theorem delta_cochainRestrict {V W : X.C} (g : W ⟶ V) (n m : ℤ)
    (z : Cochain (restrictComplex X K V) (restrictComplex X M V) n) :
    δ n m (cochainRestrict g z) = cochainRestrict g (δ n m z) := by
  by_cases h : n + 1 = m
  · apply Cochain.ext
    intro p q hpq
    have hL := δ_v n m h (cochainRestrict g z) p q hpq _ _ rfl rfl
    have hR := δ_v n m h z p q hpq _ _ rfl rfl
    simp only [hL, hR, cochainRestrict_v_eqToHom, restrictComplex_d_eqToHom g, Functor.map_add,
      Functor.map_comp, Functor.map_units_smul, Preadditive.add_comp, Preadditive.comp_add,
      Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  · simp only [δ_shape _ _ h, cochainRestrict_zero]

/-- **Restriction of cochains, as a morphism of Hom complexes.** Over an arrow `g : W ⟶ V` of
the site, restriction of cochains is a morphism of cochain complexes of abelian groups
`Hom^•(K|_V, M|_V) ⟶ Hom^•(K|_W, M|_W)`: it is additive in each degree by
`AlgebraicGeometry.RingedSite.cochainRestrict_add`, and it commutes with the differential by
`AlgebraicGeometry.RingedSite.delta_cochainRestrict`.

This is the form in which the naturality in the object of the site of [Stacks, Tag 0A94] can be
read on `HomologicalComplex.homologyMap`. -/
def homComplexRestrict {V W : X.C} (g : W ⟶ V) :
    CochainComplex.HomComplex (restrictComplex X K V) (restrictComplex X M V) ⟶
      CochainComplex.HomComplex (restrictComplex X K W) (restrictComplex X M W) where
  f n := AddCommGrpCat.ofHom (AddMonoidHom.mk' (cochainRestrict g) (cochainRestrict_add g))
  comm' i j _ := by
    ext z
    exact delta_cochainRestrict g i j z

/-- The degreewise description of `AlgebraicGeometry.RingedSite.homComplexRestrict`. -/
@[simp]
theorem homComplexRestrict_f_apply {V W : X.C} (g : W ⟶ V) (n : ℤ)
    (z : Cochain (restrictComplex X K V) (restrictComplex X M V) n) :
    (homComplexRestrict (K := K) (M := M) g).f n z = cochainRestrict g z :=
  rfl

/-! ### The local description is compatible with restriction -/

namespace SheafHomComplex

/-- **The cochain of a restricted section is the restricted cochain.** The degree-`n` cochain
from `K|_W` to `M|_W` attached by the local description to the restriction along `g : W ⟶ V` of a
section of the internal Hom complex over `V` is the restriction of the cochain attached to that
section over `V`.

This is the field `AlgebraicGeometry.RingedSite.SheafHomComplex.restrict_natural`, read as an
equality of cochains instead of pointwise on local sections of `K`. -/
theorem sectionsEquiv_restrictSection (H : SheafHomComplex X K M) {V W : X.C} (g : W ⟶ V)
    (n : ℤ) (s : (H.obj.X n).val.obj (op V)) :
    H.sectionsEquiv W n (restrictSection X g s) = cochainRestrict g (H.sectionsEquiv V n s) := by
  apply Cochain.ext
  intro p q hpq
  rw [cochainRestrict_v]
  ext ⟨T⟩ x
  exact H.sectionsEquiv_restrict g n p q hpq s T.hom x

end SheafHomComplex

end AlgebraicGeometry.RingedSite

end
