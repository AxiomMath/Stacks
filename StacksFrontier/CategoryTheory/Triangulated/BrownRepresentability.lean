module

public import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksFrontier.CategoryTheory.Triangulated.WeakBrownRepresentability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Brown representability

This file collects the formalizations of [Stacks, Tag 0A8F], [Stacks, Tag 0A8G],
[Stacks, Tag 0GYH].

## References

* [Stacks, Tag 0A8F](https://stacks.math.columbia.edu/tag/0A8F)
* [Stacks, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
-/

section

/-!
# Brown representability

Let `D` be a triangulated category with arbitrary direct sums which is *compactly generated*:
there is a set `E i`, `i : ι`, of compact objects of `D` such that `⨁ i, E i` is a (weak)
generator of `D`. Brown representability, in the form due to Neeman, says that a contravariant
cohomological functor `H : Dᵒᵖ ⥤ AddCommGrpCat` which transforms direct sums into products is
representable, i.e. `H ≅ Hom(-, X)` for some object `X` of `D`. Its principal consequence is the
existence of adjoints: an exact functor `F : D ⥤ D'` which transforms direct sums into direct sums
has a right adjoint `G`, and `G` is again exact, because for each object `Y` of `D'` the
cohomological functor `W ↦ Hom_{D'}(F W, Y)` satisfies the hypotheses of Brown representability
and so is represented by the object `G Y`.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_preadditiveYoneda_of_compactlyGenerated`:
  Brown representability.
* `CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`:
  an exact, direct-sum-preserving functor out of a compactly generated triangulated category
  has an exact right adjoint.

## Implementation notes

Vocabulary, term by term. A *contravariant cohomological functor* on `D` with values in abelian
groups is a functor `H : Dᵒᵖ ⥤ AddCommGrpCat` with `H.IsHomological`: `Dᵒᵖ` is pretriangulated
and `H` takes distinguished triangles to exact sequences, which is exactly the long exact
cohomology sequence of the source (`Functor.map_distinguished_op_exact`). *Transforms direct
sums into products* is `PreservesLimitsOfShape (Discrete α) H` for every `α`: a direct sum in
`D` is a product in `Dᵒᵖ`, and `H` is asked to send it to the product of the values. A *compact*
object `K` is one for which `⨁ i, Hom(K, X i) ⟶ Hom(K, ⨁ i, X i)` is bijective, i.e. for which
the covariant `Hom`-functor `preadditiveCoyoneda.obj (op K)` preserves direct sums; only the
infinite direct sums carry content here, since an additive functor always preserves finite
biproducts. *Representable* is pinned as an isomorphism with `preadditiveYoneda.obj X`, the
`Hom(-, X)` of abelian groups, rather than with its underlying set-valued functor: the
statement of the source is about `H` with its additive structure. An *exact functor of
triangulated categories* is a functor with a `Functor.CommShift ℤ` structure which is
`Functor.IsTriangulated`.

`⨁ i, E i` generating `D` is stated in the equivalent form that no nonzero object is right
orthogonal to all shifts of all the `E i`, i.e. `((ofObj E).shiftClosure ℤ).rightOrthogonal`
consists of zero objects, which avoids referring to the object `⨁ i, E i` and to the
identification `Hom(⨁ i, E i, Y) = ∏ i, Hom(E i, Y)`. The two agree: a nonzero map
`⨁ i, E i ⟶ Y⟦n⟧` is the same thing as a family of maps `E i ⟶ Y⟦n⟧` not all zero, and
`Hom(E i⟦a⟧, Y) ≅ Hom(E i, Y⟦-a⟧)`.

The index type `ι` of the generating family and the index types of the direct sums are taken in
the universe `v` of the morphisms of `D`, which is where the values of `H` live too; this is the
locally small situation of the source, and it is what makes the hypotheses non-vacuous. The proof
needs direct sums indexed by `ι`, by the pairs `(i, a)` with `a : H.obj (op (E i))` — still a
`Type v` — and by `ℕ` (a homotopy colimit); the last of these follows from `HasCoproducts.{v} D`
by transporting along `Discrete ℕ ≌ Discrete (ULift.{v} ℕ)`.

Brown representability is obtained from weak Brown representability [Stacks, Tag 0GYG], applied
to the family `(i, n) ↦ (E i)⟦n⟧` of all shifts of the members of the given family. Condition (1)
of that tag, that every nonzero object receives a nonzero morphism from a member of the family, is
the generation hypothesis read through `rightOrthogonal_shiftClosure_ofObj_iff`: right
orthogonality to the shift closure of a family is the vanishing of every morphism from every shift
of every member. Condition (2), that a morphism from a member of the family into a countable direct
sum `∐ X` factors through a direct sum of members of the family, holds for the stronger reason that
such a morphism is a *finite* sum `∑ j ∈ S, β j ≫ Sigma.ι X j` of morphisms through the summands:
the factorization is then through the direct sum of the constant family, by the sum of the
coprojections indexed by `S`. That finite decomposition is what compactness says; it is proved here
from the assumption that `preadditiveCoyoneda.obj (op (E i))` preserves direct sums, since the
morphisms into `∐ X` admitting such a decomposition are exactly the range of the canonical map
`⨁ j, (E i ⟶ X j) → (E i ⟶ ∐ X)`, hence a subgroup of `E i ⟶ ∐ X` containing the images of the
coprojections, and a colimit of abelian groups admits no proper subgroup of its vertex containing
the images of the legs of the cocone (`mem_of_isColimit`). Compactness transfers along an
adjunction, and that is how it is obtained for the shifts: if `F ⊣ G` with `F` additive and `G`
preserving colimits of the shape considered, then `Hom(F K, -) ≅ G ⋙ Hom(K, -)` by the additive
hom-set bijection `Adjunction.homAddEquiv`, so `F K` is compact as soon as `K` is, and for a shift
this is the adjunction underlying the equivalence `shiftEquiv D n`.

The existence of the adjoint is three steps. That `W ↦ Hom_{D'}(F W, Y)` transforms direct sums
into products is `preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj`: a direct sum
indexed by `Discrete α` in `D` is a product indexed by `(Discrete α)ᵒᵖ` in `Dᵒᵖ`, and `Discrete α`
is its own opposite, so `F.op` transforms such products into products, while `Hom_{D'}(-, Y)`
transforms all limits into limits (`preservesLimits_preadditiveYoneda_obj`, which is stated for
index categories of the size of the morphisms of `D'`, and `Discrete α` for `α : Type v` is of that
size). That the partial right adjoint is defined at `Y` is
`rightAdjointObjIsDefined_of_compactlyGenerated`, the one appeal to Brown representability, and
exactness of the adjoint is `exists_isTriangulated_rightAdjoint_of_isLeftAdjoint`, which over a
pretriangulated target holds for any exact functor with a right adjoint and uses nothing about the
generating family. Brown representability produces an isomorphism of `AddCommGrpCat`-valued
functors, while the domain of definition of the partial right adjoint,
`Functor.rightAdjointObjIsDefined`, is phrased with the `Type`-valued Yoneda embedding; the passage
between the two is a whiskering with the forgetful functor, `preadditiveYoneda.obj X ⋙
forget AddCommGrpCat` being `yoneda.obj X`.

Where the source says the right adjoint is *exact*, the conclusion asserts the stronger
`Adjunction.IsTriangulated`: the adjunction `F ⊣ G` is compatible with the shifts by `ℤ`
(`Adjunction.CommShift`, i.e. the unit commutes with the shift) and both adjoints are
triangulated functors. Exactness of `G` alone is not expressible without first choosing a
`Functor.CommShift ℤ` structure on `G`, so that structure is part of the existential; the
triangulated adjunction is the datum a user of this proposition wants, and it determines the
`CommShift` structure on `G` uniquely (`Adjunction.CommShift.compatibilityUnit_unique_right`).
For the adjoint, `D` and `D'` are given the *same* morphism universe `v`, which is what makes
`W ↦ Hom_{D'}(F W, Y)` a functor to abelian groups of the size Brown representability is stated
for, and `D'` is asked only to be pretriangulated: the octahedron axiom is used on the source
category `D`, never on the target.

## References

* [Amnon Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown
  representability*, Theorems 3.1 and 4.1][Neeman-Grothendieck]
* [Stacks project, Tag 0A8F](https://stacks.math.columbia.edu/tag/0A8F)
* [Stacks project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks project, Tag 0A8B](https://stacks.math.columbia.edu/tag/0A8B), a functor with a
  pointwise defined partial right adjoint has a right adjoint
* [Stacks project, Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D), the right adjoint of an
  exact functor is exact
* [Stacks project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG), weak Brown
  representability
-/

@[expose] public section

universe w w' v u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated.Opposite Opposite

namespace CategoryTheory.Pretriangulated

/-! ### Compactness as a finite decomposition of morphisms into a direct sum -/

/-- A colimit of abelian groups is exhausted by any subgroup of its vertex which contains the
images of the legs of the cocone: the quotient by such a subgroup receives the zero map from the
colimit, since it does from every `F.obj j`. -/
lemma mem_of_isColimit {J : Type w} [Category.{u} J] {F : J ⥤ AddCommGrpCat.{v}}
    {c : Cocone F} (hc : IsColimit c) (S : AddSubgroup c.pt)
    (hS : ∀ (j : J) (x : F.obj j), ConcreteCategory.hom (c.ι.app j) x ∈ S) (a : c.pt) : a ∈ S := by
  have h : AddCommGrpCat.ofHom (QuotientAddGroup.mk' S) = 0 := by
    refine hc.hom_ext fun j ↦ ?_
    ext x
    simpa using (QuotientAddGroup.eq_zero_iff _).2 (hS j x)
  simpa [QuotientAddGroup.eq_zero_iff] using ConcreteCategory.congr_hom h a

section

variable {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} {K : C} {X : J → C}
  [HasCoproduct X]

/-- A morphism from a compact object into a direct sum is a finite sum of morphisms through the
summands: the surjectivity half of the bijectivity which defines compactness in
[Stacks, Tag 07LS]. Indeed the morphisms of that form are the range of the canonical map
`DirectSum.toAddMonoid fun j ↦ Preadditive.rightComp K (Sigma.ι X j)` of that tag, a subgroup of
`K ⟶ ∐ X` which contains every `f ≫ Sigma.ι X j`, and `Hom(K, -)` carries the direct sum to a
colimit of abelian groups, which no proper such subgroup exhausts. -/
private lemma exists_sum_comp_sigmaι (K : C) (X : J → C) [HasCoproduct X]
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op K))] (α : K ⟶ ∐ X) :
    ∃ (S : Finset J) (β : ∀ j, K ⟶ X j), α = ∑ j ∈ S, β j ≫ Sigma.ι X j := by
  classical
  obtain ⟨b, rfl⟩ := mem_of_isColimit
    (isColimitOfPreserves (preadditiveCoyoneda.obj (op K)) (coproductIsCoproduct X))
    (DirectSum.toAddMonoid fun j ↦ Preadditive.rightComp K (Sigma.ι X j)).range
    (fun j f ↦ ⟨DirectSum.of _ j.as f, DirectSum.toAddMonoid_of _ _ _⟩) α
  refine ⟨b.support, fun j ↦ b j, ?_⟩
  conv_lhs => rw [← DirectSum.sum_support_of b]
  simp [Preadditive.rightComp]

end

/-! ### Compactness of the shifts -/

section

variable {C : Type u} {C' : Type u'} [Category.{v} C] [Category.{v} C'] [Preadditive C]
  [Preadditive C'] {J : Type w} [Category.{w'} J]

/-- A left adjoint carries a compact object to a compact object: if `F ⊣ G` with `F` additive and
`G` preserving colimits of shape `J`, and if `Hom(K, -)` preserves colimits of shape `J`, then so
does `Hom(F K, -)`, along the isomorphism `Hom(F K, -) ≅ G ⋙ Hom(K, -)` given by the additive
hom-set bijection of the adjunction. -/
private lemma preservesColimitsOfShape_preadditiveCoyoneda_obj_op_of_adjunction
    {F : C ⥤ C'} {G : C' ⥤ C} (adj : F ⊣ G) [F.Additive] (K : C)
    [PreservesColimitsOfShape J (preadditiveCoyoneda.obj (op K))]
    [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (preadditiveCoyoneda.obj (op (F.obj K))) :=
  preservesColimitsOfShape_of_natIso (F := G ⋙ preadditiveCoyoneda.obj (op K))
    (NatIso.ofComponents (fun Y ↦ (adj.homAddEquiv K Y).toAddCommGrpIso)
      (fun {Y Y'} g ↦ by
        ext f
        exact adj.homEquiv_naturality_right f g)).symm

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D] {A : Type*} [AddGroup A] [HasShift D A]

/-- A shift of a compact object is compact, the shift functors being equivalences. -/
private lemma preservesColimitsOfShape_shift (K : D) (n : A) [(shiftFunctor D n).Additive]
    (J : Type w) [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op K))] :
    PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op (K⟦n⟧))) :=
  have adj : shiftFunctor D n ⊣ shiftFunctor D (-n) := (shiftEquiv D n).toAdjunction
  preservesColimitsOfShape_preadditiveCoyoneda_obj_op_of_adjunction adj K

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Compactness against the index type `ULift ℕ` in the universe of the morphisms gives
compactness against `ℕ`, by transport along `Discrete (ULift ℕ) ≌ Discrete ℕ`. -/
private lemma preservesColimitsOfShape_nat (K : C)
    [PreservesColimitsOfShape (Discrete (ULift.{v} ℕ)) (preadditiveCoyoneda.obj (op K))] :
    PreservesColimitsOfShape (Discrete ℕ) (preadditiveCoyoneda.obj (op K)) :=
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ))
    (preadditiveCoyoneda.obj (op K))

end

/-! ### The two conditions of weak Brown representability -/

section

variable {C : Type u} [Category.{v} C] [Preadditive C] {A : Type*} [AddGroup A] [HasShift C A]
  {ι : Type w} (E : ι → C)

/-- An object is right orthogonal to the shift closure of a family of objects exactly when every
morphism to it from every shift of every member of the family vanishes. -/
lemma rightOrthogonal_shiftClosure_ofObj_iff (Y : C) :
    ((ofObj E).shiftClosure A).rightOrthogonal Y ↔
      ∀ (i : ι) (a : A) (f : (E i)⟦a⟧ ⟶ Y), f = 0 := by
  refine ⟨fun h i a f ↦ h f ⟨E i, a, Iso.refl _, ofObj_apply E i⟩, ?_⟩
  rintro h Z f ⟨W, a, e, ⟨i⟩⟩
  rw [← cancel_epi e.inv, comp_zero]
  exact h i a _

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ] {ι : Type v} (E : ι → D)

/-- The generation hypothesis says that every nonzero object receives a nonzero morphism from some
shift of some member of the family: condition (1) of [Stacks, Tag 0GYG]. -/
private lemma exists_ne_zero_of_not_isZero
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y)
    (X : D) (hX : ¬ IsZero X) :
    ∃ (p : ι × ULift.{v} ℤ) (f : (E p.1)⟦p.2.down⟧ ⟶ X), f ≠ 0 := by
  by_contra hc
  simp only [not_exists, not_ne_iff] at hc
  exact hX <| hE X <| (rightOrthogonal_shiftClosure_ofObj_iff E X).2
    fun i a f ↦ hc (i, ULift.up a) f

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [HasCoproducts.{v} D] {ι : Type v} (E : ι → D)

/-- A morphism from a shift of a member of the family into a countable direct sum factors through
a direct sum of shifts of members of the family: condition (2) of [Stacks, Tag 0GYG]. It even
factors through the direct sum of the constant family, by the sum of the coprojections indexed by
the finite set carrying the decomposition of the morphism. -/
private lemma exists_factorsThroughSigma
    [∀ (i : ι) (α : Type v),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (X : ℕ → D) (p : ι × ULift.{v} ℤ) (α : (E p.1)⟦p.2.down⟧ ⟶ ∐ X) :
    ∃ (q : ℕ → ι × ULift.{v} ℤ) (β : ∀ m, (E (q m).1)⟦(q m).2.down⟧ ⟶ X m)
      (γ : (E p.1)⟦p.2.down⟧ ⟶ ∐ fun m ↦ (E (q m).1)⟦(q m).2.down⟧),
      α = γ ≫ Limits.Sigma.map β := by
  have := preservesColimitsOfShape_nat (E p.1)
  have := preservesColimitsOfShape_shift (E p.1) p.2.down ℕ
  obtain ⟨S, β, hβ⟩ := exists_sum_comp_sigmaι ((E p.1)⟦p.2.down⟧) X α
  refine ⟨fun _ ↦ p, β, ∑ m ∈ S, Sigma.ι (fun _ : ℕ ↦ (E p.1)⟦p.2.down⟧) m, ?_⟩
  simp [hβ, Preadditive.sum_comp, Sigma.ι_map]

end

/-! ### Brown representability -/

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{v} D]

/-- **Brown representability**: let `D` be a triangulated category with arbitrary direct sums
which is compactly generated, i.e. there is a family `E : ι → D` of compact objects (each
`preadditiveCoyoneda.obj (op (E i))` preserves direct sums) whose direct sum generates `D` (the
only objects right orthogonal to all shifts of the `E i` are the zero objects). Then every
contravariant cohomological functor `H : Dᵒᵖ ⥤ AddCommGrpCat` which transforms direct sums into
products is representable: `H ≅ Hom(-, X)` for some `X : D`. -/
@[stacks 0A8F]
public theorem exists_iso_preadditiveYoneda_of_compactlyGenerated
    {ι : Type v} (E : ι → D)
    [∀ (i : ι) (α : Type v),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y)
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    [∀ α : Type v, PreservesLimitsOfShape (Discrete α) H] :
    ∃ X : D, Nonempty (H ≅ preadditiveYoneda.obj X) := by
  obtain ⟨X, ⟨e⟩⟩ :=
    exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma
      (fun p : ι × ULift.{v} ℤ ↦ (E p.1)⟦p.2.down⟧)
      (exists_ne_zero_of_not_isZero E hE) (exists_factorsThroughSigma E) H
  exact ⟨X, ⟨e.symm⟩⟩

end

/-! ### Existence of an exact right adjoint -/

section Yoneda

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D] [Preadditive D]

/-- If `F : C ⥤ D` transforms direct sums indexed by `α` into direct sums, then the contravariant
functor `W ↦ Hom_D(F W, Y)` transforms them into products. -/
private lemma preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj (F : C ⥤ D) (Y : D)
    (α : Type v) [PreservesColimitsOfShape (Discrete α) F] :
    PreservesLimitsOfShape (Discrete α) (F.op ⋙ preadditiveYoneda.obj Y) :=
  have := preservesLimitsOfShape_op (Discrete α) F
  inferInstance

/-- An isomorphism `Hom_C(-, X) ≅ Hom_D(F -, Y)` of `AddCommGrpCat`-valued functors puts `Y` in
the domain of definition of the partial right adjoint of `F`, which is phrased with the
`Type`-valued Yoneda embedding: `Hom_C(-, X) ⋙ forget AddCommGrpCat` *is* `yoneda.obj X`. -/
private lemma rightAdjointObjIsDefined_of_iso_preadditiveYoneda [Preadditive C]
    {F : C ⥤ D} {Y : D} {X : C}
    (e : preadditiveYoneda.obj X ≅ F.op ⋙ preadditiveYoneda.obj Y) :
    F.rightAdjointObjIsDefined Y :=
  Functor.IsRepresentable.mk' (X := X)
    (show yoneda.obj X ≅ F.op ⋙ yoneda.obj Y from
      Functor.isoWhiskerRight e (forget AddCommGrpCat))

end Yoneda

section Adjoint

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v} D']
  [HasZeroObject D] [HasZeroObject D'] [Preadditive D] [Preadditive D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']

/-- An exact functor of pretriangulated categories which has a right adjoint has an exact one:
the right adjoint carries a unique shift structure compatible with the adjunction, and for it
the adjunction is triangulated. This is [Stacks, Tag 0A8D]. -/
@[sga "4 XVII 2.2.13.1" "special case", sga "4½ Etat_0 2.6.7" "partial"]
private lemma exists_isTriangulated_rightAdjoint_of_isLeftAdjoint (F : D ⥤ D') [F.CommShift ℤ]
    [F.IsTriangulated] [F.IsLeftAdjoint] :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated := by
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  exact ⟨F.rightAdjoint, adj, inferInstance, Adjunction.IsTriangulated.mk' adj⟩

variable [IsTriangulated D] [HasCoproducts.{v} D]

/-- Under the hypotheses of [Stacks, Tag 0A8G], the partial right adjoint of `F` is defined at
every object `Y` of `D'`: the cohomological functor `W ↦ Hom_{D'}(F W, Y)` transforms direct sums
into products, hence is represented by an object of `D` by Brown representability
[Stacks, Tag 0A8F], and being represented is exactly what being in the domain of definition of the
partial right adjoint means. -/
private lemma rightAdjointObjIsDefined_of_compactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type v, PreservesColimitsOfShape (Discrete α) F]
    {ι : Type v} (E : ι → D)
    [∀ (i : ι) (α : Type v),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y) (Y : D') :
    F.rightAdjointObjIsDefined Y := by
  have : ∀ α : Type v,
      PreservesLimitsOfShape (Discrete α) (F.op ⋙ preadditiveYoneda.obj Y) := fun α ↦
    preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj F Y α
  obtain ⟨X, ⟨e⟩⟩ := exists_iso_preadditiveYoneda_of_compactlyGenerated
    E hE (F.op ⋙ preadditiveYoneda.obj Y)
  exact rightAdjointObjIsDefined_of_iso_preadditiveYoneda e.symm

/-- Let `D` be a triangulated category with arbitrary direct sums which is compactly generated,
i.e. there is a family `E : ι → D` of compact objects (each `preadditiveCoyoneda.obj (op (E i))`
preserves direct sums) whose direct sum generates `D` (the only objects right orthogonal to all
shifts of the `E i` are the zero objects). Let `F : D ⥤ D'` be an exact functor of triangulated
categories which transforms direct sums into direct sums. Then `F` has a right adjoint `G`,
which is again exact: the adjunction `F ⊣ G` is a triangulated adjunction for a (unique)
`Functor.CommShift ℤ` structure on `G`. -/
@[stacks 0A8G, sga "4 XVII 2.2.13.1" "Triangulated case"]
public theorem exists_isTriangulated_rightAdjoint_of_compactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type v, PreservesColimitsOfShape (Discrete α) F]
    {ι : Type v} (E : ι → D)
    [∀ (i : ι) (α : Type v),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ Y : D, ((ofObj E).shiftClosure ℤ).rightOrthogonal Y → IsZero Y) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated :=
  have : F.IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (eq_top_iff.2 fun Y _ ↦
      rightAdjointObjIsDefined_of_compactlyGenerated F E hE Y)
  exists_isTriangulated_rightAdjoint_of_isLeftAdjoint F

end Adjoint

end CategoryTheory.Pretriangulated

end

end

section

/-!
# Existence of an exact right adjoint, via weak Brown representability

Let `D` be a triangulated category with direct sums, and suppose there is a family `E : ι → D`
of objects of `D` satisfying conditions (1) and (2) of weak Brown representability
[Stacks, Tag 0GYG]:

1. every nonzero object `X` of `D` receives a nonzero morphism `E i ⟶ X` from some member of the
   family, and
2. for every family `X : ℕ → D`, every morphism `α : E i ⟶ ∐ X` into its direct sum factors as
   `α = γ ≫ Sigma.map β` for some `j : ℕ → ι`, morphisms `β n : E (j n) ⟶ X n` and
   `γ : E i ⟶ ∐ fun n ↦ E (j n)`.

Let `F : D ⥤ D'` be an exact functor of triangulated categories which transforms direct sums into
direct sums. Then `F` has a right adjoint `G`, and `G` is again exact. The proof is one appeal to
weak Brown representability per object `Y` of `D'`: the contravariant functor
`W ↦ Hom_{D'}(F W, Y)` is cohomological because `F` is exact and transforms direct sums into
products because `F` transforms direct sums into direct sums, so it is represented by an object
`G Y` of `D`, and an adjoint assembles from these representing objects.

## Main results

* `exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma` (in the
  `CategoryTheory.Pretriangulated` namespace): an exact, direct-sum-preserving functor out of a
  triangulated category with a set of generators in the sense of [Stacks, Tag 0GYG] has an exact
  right adjoint.

## Implementation notes

Vocabulary, term by term. An *exact functor of triangulated categories* is a functor `F` carrying
a `Functor.CommShift ℤ` structure (a compatible identification `F(W⟦n⟧) ≅ F(W)⟦n⟧`) which is
`Functor.IsTriangulated`: it sends distinguished triangles to distinguished triangles.
*Transforms direct sums into direct sums* is `PreservesColimitsOfShape (Discrete α) F` for every
`α : Type (max w v)`; it asks nothing of `D'` beyond the coproducts `D'` happens to have, and only
the infinite direct sums carry content, an additive functor preserving finite biproducts always.

The hypotheses `E`, `hE`, `hE'` and `HasCoproducts.{max w v} D` are those of
`exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma` (weak Brown representability,
[Stacks, Tag 0GYG]), transcribed unchanged, including its universe discipline: `ι : Type w` (the
source's *set* `ℰ` is a family indexed by a type, which is where its smallness lives) and direct
sums of families indexed by `Type (max w v)`, the size in which the representing objects are
constructed there. Conditions (1) and (2) are spelled out as the two hypotheses `hE` and `hE'`
rather than through a named predicate on `E`, because that is how they are spelled there; the two
statements are meant to be read side by side. Since they are transcribed rather than cited, the
statement itself refers to nothing from weak Brown representability; the appeal to it is made by
the proof. This is the sibling of
`exists_isTriangulated_rightAdjoint_of_compactlyGenerated` ([Stacks, Tag 0A8G]), the same
proposition for a compactly generating family, and the two differ only in that hypothesis.
The index type `α` of the direct sums that `F` must preserve is `Type (max w v)` and not `Type v`:
weak Brown representability asks for `W ↦ Hom_{D'}(F W, Y)` to turn `Discrete J`-indexed direct
sums into products for every `J : Type (max w v)`, the size in which it builds the representing
object, and that functor does so exactly when `F` preserves those direct sums.

Two departures from the form of the source, both shared with the sibling proposition
[Stacks, Tag 0A8G]. First, `D` and `D'` are given the *same* morphism universe `v`, the locally
small situation of the source: this is what makes `W ↦ Hom_{D'}(F W, Y)` a functor to abelian
groups of the size that weak Brown representability is stated for. Second, `D'` is asked only to
be pretriangulated, the octahedron axiom being used on `D` alone (through 0GYG).

Where the source says the right adjoint is *exact*, the conclusion asserts the stronger
`Adjunction.IsTriangulated`: the adjunction `F ⊣ G` is compatible with the shifts by `ℤ`
(`Adjunction.CommShift`) and both adjoints are triangulated functors. Exactness of `G` alone is
not expressible without first choosing a `Functor.CommShift ℤ` structure on `G`, so that structure
is part of the existential; it is determined uniquely by the adjunction
(`Adjunction.CommShift.compatibilityUnit_unique_right`), and the triangulated adjunction is the
datum a user of this proposition wants.

The argument is three steps and two of them are recorded separately.
`preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj'`: the cohomological functor
`W ↦ Hom_{D'}(F W, Y)`, which is `F.op ⋙ preadditiveYoneda.obj Y : Dᵒᵖ ⥤ AddCommGrpCat`,
transforms direct sums into products as soon as `F` transforms direct sums into direct sums, a
direct sum indexed by `α` in `D` being a product indexed by `Discrete α` in `Dᵒᵖ`.
`rightAdjointObjIsDefined_of_iso_preadditiveYoneda`: an object representing that functor puts `Y`
in the domain of definition of the partial right adjoint of `F`.
`exists_isTriangulated_rightAdjoint_of_isLeftAdjoint'`: over a pretriangulated target every exact
functor with a right adjoint has an exact one, by `Adjunction.rightAdjointCommShift`,
`Adjunction.commShift_of_leftAdjoint` and `Adjunction.IsTriangulated.mk'`; this needs no hypothesis
on the generating family. What is left is the one appeal to weak Brown representability and the
passage from a pointwise defined partial right adjoint to an adjoint,
`Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`.

That `W ↦ Hom_{D'}(F W, Y)` is homological is the composition of the triangulated functor `F.op`
with the homological functor `preadditiveYoneda.obj Y`. Weak Brown representability produces an
isomorphism of `AddCommGrpCat`-valued functors, while the domain of definition of the partial right
adjoint, `Functor.rightAdjointObjIsDefined`, is phrased with the `Type`-valued Yoneda embedding.
The passage between the two is a whiskering with the forgetful functor:
`preadditiveYoneda.obj X ⋙ forget AddCommGrpCat` *is* `yoneda.obj X`.

Mathlib's `preservesLimits_preadditiveYoneda_obj` says that `Hom(-, Y) : Dᵒᵖ ⥤ AddCommGrpCat`
transforms limits into limits for index categories of the size of the morphisms of `D`, whereas
here the index types are of size `max w v`. The `Type`-valued `yoneda` preserves limits of every
size, and the forgetful functor of `AddCommGrpCat` reflects them, so the same statement holds with
no size restriction at all; that is `preservesLimitsOfSize_preadditiveYoneda_obj`, stated here for
want of it in Mathlib. It is exactly what the `max w v` of weak Brown representability costs: in
the sibling proposition [Stacks, Tag 0A8G] the direct sums are indexed by `Type v`, `Discrete α` is
then a category of the size Mathlib's instance is stated for, and no such lemma is needed.

## References

* [Stacks project, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
* [Stacks project, Tag 0A8B](https://stacks.math.columbia.edu/tag/0A8B), a functor with a
  pointwise defined partial right adjoint has a right adjoint
* [Stacks project, Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D), the right adjoint of an
  exact functor is exact
* [Stacks project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG), a weak version of
  Theorem A of H. Krause, *A Brown representability theorem via coherent functors*.
-/

@[expose] public section

universe w w' v u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory.Pretriangulated

section Yoneda

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v} D']

/-- The functor `Hom(-, Y) : Dᵒᵖ ⥤ AddCommGrpCat` transforms limits of any size into limits: it
does so after applying the forgetful functor to types, where it is `yoneda.obj Y`, and the
forgetful functor of `AddCommGrpCat` reflects limits of every shape. -/
@[sga "2 IV 1.2" "Forward implication"]
private lemma preservesLimitsOfSize_preadditiveYoneda_obj [Preadditive D] (Y : D) :
    PreservesLimitsOfSize.{w', w} (preadditiveYoneda.obj Y) where
  preservesLimitsOfShape {J _} :=
    have : PreservesLimitsOfShape J (preadditiveYoneda.obj Y ⋙ forget AddCommGrpCat) :=
      (inferInstance : PreservesLimitsOfShape J (yoneda.obj Y))
    preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)

/-- If `F` transforms `α`-indexed direct sums into direct sums, then the contravariant functor
`W ↦ Hom_{D'}(F W, Y)` transforms them into products: an `α`-indexed direct sum in `D` is a
`Discrete α`-indexed product in `Dᵒᵖ`, which `F.op` transforms into a product because `Discrete α`
is its own opposite, and `Hom_{D'}(-, Y)` transforms products of any size into products. -/
private lemma preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj' [Preadditive D']
    (F : D ⥤ D') (Y : D') (α : Type w') [PreservesColimitsOfShape (Discrete α) F] :
    PreservesLimitsOfShape (Discrete α) (F.op ⋙ preadditiveYoneda.obj Y) :=
  have := preservesLimitsOfShape_op (Discrete α) F
  have := preservesLimitsOfSize_preadditiveYoneda_obj.{w', w'} Y
  inferInstance

end Yoneda

section Adjunction

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v} D']
  [HasZeroObject D] [HasZeroObject D'] [Preadditive D] [Preadditive D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']

/-- An exact functor of pretriangulated categories which has a right adjoint has an exact one:
the right adjoint carries a unique shift structure compatible with the adjunction, and for it
the adjunction is triangulated. This is [Stacks, Tag 0A8D]. -/
@[sga "4 XVII 2.2.13.1" "special case", sga "4½ Etat_0 2.6.7" "partial"]
private alias exists_isTriangulated_rightAdjoint_of_isLeftAdjoint' := exists_isTriangulated_rightAdjoint_of_isLeftAdjoint

end Adjunction

section BrownRepresentability

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v} D']
  [HasZeroObject D] [HasZeroObject D'] [Preadditive D] [Preadditive D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [IsTriangulated D] [HasCoproducts.{max w v} D]

/-- Under the hypotheses of [Stacks, Tag 0GYH], the partial right adjoint of `F` is defined at
every object `Y` of `D'`: the cohomological functor `W ↦ Hom_{D'}(F W, Y)` transforms direct sums
into products, hence is represented by an object of `D` by weak Brown representability
[Stacks, Tag 0GYG], and being represented is exactly what being in the domain of definition of the
partial right adjoint means. -/
private lemma rightAdjointObjIsDefined_of_generating_of_factorsThroughSigma
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max w v), PreservesColimitsOfShape (Discrete α) F]
    {ι : Type w} (E : ι → D)
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ X n)
      (γ : E i ⟶ ∐ fun n ↦ E (j n)), α = γ ≫ Limits.Sigma.map β) (Y : D') :
    F.rightAdjointObjIsDefined Y := by
  have : ∀ J : Type (max w v),
      PreservesLimitsOfShape (Discrete J) (F.op ⋙ preadditiveYoneda.obj Y) := fun J ↦
    preservesLimitsOfShape_discrete_op_comp_preadditiveYoneda_obj' F Y J
  obtain ⟨X, ⟨e⟩⟩ := exists_iso_preadditiveYoneda_of_generating_of_factorsThroughSigma
    E hE hE' (F.op ⋙ preadditiveYoneda.obj Y)
  exact rightAdjointObjIsDefined_of_iso_preadditiveYoneda e

/-- Let `D` be a triangulated category with direct sums and let `E : ι → D` be a family of
objects satisfying conditions (1) and (2) of weak Brown representability
[Stacks, Tag 0GYG]: every nonzero object of `D` receives a nonzero morphism from some `E i`, and
every morphism from some `E i` to a countable direct sum `∐ X`, `X : ℕ → D`, factors through a
direct sum `∐ fun n ↦ E (j n)` of members of the family via a direct sum of morphisms
`E (j n) ⟶ X n`. Let `F : D ⥤ D'` be an exact functor of triangulated categories which transforms
direct sums into direct sums. Then `F` has a right adjoint `G`, which is again exact: the
adjunction `F ⊣ G` is a triangulated adjunction for a (unique) `Functor.CommShift ℤ` structure
on `G`. -/
@[stacks 0GYH, sga "4 XVII 2.2.13.1" "Triangulated case"]
public theorem exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max w v), PreservesColimitsOfShape (Discrete α) F]
    {ι : Type w} (E : ι → D)
    (hE : ∀ X : D, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0)
    (hE' : ∀ (X : ℕ → D) (i : ι) (α : E i ⟶ ∐ X), ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ X n)
      (γ : E i ⟶ ∐ fun n ↦ E (j n)), α = γ ≫ Limits.Sigma.map β) :
    ∃ (G : D' ⥤ D) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated :=
  have : F.IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (eq_top_iff.2 fun Y _ ↦
      rightAdjointObjIsDefined_of_generating_of_factorsThroughSigma F E hE hE' Y)
  exists_isTriangulated_rightAdjoint_of_isLeftAdjoint' F

end BrownRepresentability

end CategoryTheory.Pretriangulated

end

end
