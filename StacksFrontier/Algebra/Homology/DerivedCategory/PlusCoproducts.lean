module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts

/-!
# Direct sums of uniformly bounded below families in the bounded below derived category

Let `A` be a Grothendieck abelian category.  The unbounded derived category `D(A)` has
arbitrary direct sums (`Stacks.Injectives.hasCoproducts_derivedCategory`) and the
localization functor `Q : C(A) ⥤ D(A)` computes them as termwise direct sums
(`Stacks.Injectives.derivedCategoryQ_preservesCoproducts`).  Neither statement passes to the
bounded below derived category `D⁺(A)` as it stands: `D⁺(A)` does **not** have arbitrary
direct sums.  Already for `A = ModuleCat R` the family `K i = M[i]`, `i : ℕ`, has a direct sum
in `D(A)` with nonvanishing cohomology in every degree `-i`, so no object of `D⁺(A)` can be
its direct sum.

What does hold, and what is proved here, is the statement for a family admitting a *common*
lower bound.  If `K i` is `≥ a` for every `i` then the direct sum of the `K i` in `D(A)` is
again `≥ a`, hence lies in `D⁺(A)`, where it is their direct sum; and if the `K i` are the
images of complexes `M i` that are strictly `≥ a`, that direct sum is the image of the
termwise direct sum `∐ M`.

Everything here is produced as **data**: `isColimitTermwiseDirectSumCofan` is an `IsColimit`,
not a `Nonempty (IsColimit _)`, so a consumer can form the comparison morphism out of it.

## Main results

* `DerivedCategory.isGE_of_isColimit_discrete`: a direct sum in `D(A)` of objects that are all
  `≥ a` is `≥ a`.
* `DerivedCategory.Plus.hasColimit_of_isGE`: a family in `D⁺(A)` with a common lower bound has
  a direct sum, and `DerivedCategory.Plus.preservesColimit_ι_of_isGE` says that it is computed
  in `D(A)`.
* `DerivedCategory.Plus.isColimitTermwiseDirectSumCofan`: the termwise direct sum of complexes
  that are all strictly `≥ a` is, as data, the direct sum in `D⁺(A)` of the objects they
  represent.
* `DerivedCategory.Plus.preservesColimit_of_preservesColimit_ι` and
  `DerivedCategory.Plus.preservesColimit_discrete_functor_of_unbounded`: a functor
  `D⁺(A) ⥤ D⁺(B)` induced by a functor `D(A) ⥤ D(B)` that commutes with direct sums commutes
  with direct sums of uniformly bounded below families.  This is the transfer lemma a consumer
  needs in order to read an unbounded direct sum statement on `D⁺`.
* `DerivedCategory.Plus.preservesColimit_termwiseDirectSum`: for a functor with no
  unbounded model, preservation of such a direct sum may be checked on the termwise
  direct sum.
* `DerivedCategory.Plus.strictModel`, `DerivedCategory.Plus.isStrictlyGE_strictModel` and
  `DerivedCategory.Plus.isoStrictModel`: an object of `D⁺(A)` that is `≥ a` is represented by a
  cochain complex that is *strictly* `≥ a`.  This is the `D⁺`-level packaging of
  `DerivedCategory.exists_iso_Q_obj_of_isGE`, delivered as data.
* `DerivedCategory.Plus.preservesColimit_discrete_of_termwiseDirectSum`: consequently the
  termwise criterion above, which speaks only of families of the form `ofIsGE (M i) a`, already
  gives preservation of the direct sum of an *arbitrary* family with a common lower bound.

## Implementation notes

`D⁺(A)` is the full subcategory `DerivedCategory.TStructure.t.plus.FullSubcategory` of `D(A)`.
Direct sums in it are therefore obtained from `Limits.createsColimitFullSubcategoryInclusion`,
which needs exactly the statement that the ambient direct sum stays in the subcategory; that
statement is `isGE_of_isColimit_discrete`.  Since the inclusion is fully faithful it also
reflects colimits, which is what turns an ambient `IsColimit` into one in `D⁺(A)` without any
choice, and what makes the transfer lemma a one-line consequence of
`Limits.preservesColimit_of_reflects_of_preserves`.

`isGE_of_isColimit_discrete` is proved by replacing each object by a complex that is *strictly*
`≥ a` (`DerivedCategory.exists_iso_Q_obj_of_isGE`); the termwise direct sum of those is
strictly `≥ a` degreewise, and `Q` sends it to the direct sum.  No statement that cohomology
commutes with direct sums is needed.

The model of the derived category is arbitrary throughout: every statement takes
`[HasDerivedCategory A]` (and `[HasDerivedCategory B]` for the transfer lemmas).
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] {I : Type w}

/-- A termwise direct sum of cochain complexes that are all strictly `≥ a` is strictly `≥ a`:
in each degree `< a` it is a direct sum of zero objects. -/
lemma isStrictlyGE_coproduct (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] [HasColimitsOfShape (Discrete I) A] :
    (∐ M).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  exact (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) n)
    (coproductIsCoproduct M)).hom_ext
    fun j ↦ ((M j.as).isZero_of_isStrictlyGE a n hn).eq_of_src _ _

end CochainComplex

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory A]

section Unbounded

variable {I : Type w} {a : ℤ}

/-- **A direct sum in `D(A)` of objects that are all `≥ a` is `≥ a`.**  Equivalently, the
objects `≥ a` form a subcategory of `D(A)` closed under direct sums of any shape. -/
lemma isGE_of_isColimit_discrete {F : Discrete I ⥤ DerivedCategory A}
    (hF : ∀ j, (F.obj j).IsGE a) {c : Cocone F} (hc : IsColimit c) : c.pt.IsGE a := by
  classical
  have h : ∀ i : I, ∃ M : CochainComplex A ℤ,
      M.IsStrictlyGE a ∧ Nonempty (F.obj ⟨i⟩ ≅ Q.obj M) := fun i ↦ by
    have := hF ⟨i⟩
    obtain ⟨M, hM, hiso⟩ := (F.obj ⟨i⟩).exists_iso_Q_obj_of_isGE a
    exact ⟨M, hM, hiso⟩
  choose M hM hiso using h
  have hM' : ∀ i, (M i).IsStrictlyGE a := hM
  have hsum : (∐ M).IsStrictlyGE a := CochainComplex.isStrictlyGE_coproduct M a
  have hQ : IsColimit ((Q (C := A)).mapCocone (Cofan.mk (∐ M) (Sigma.ι M))) :=
    isColimitOfPreserves _ (coproductIsCoproduct M)
  have e : Q.obj (∐ M) ≅ c.pt :=
    (hc.coconePointsIsoOfNatIso hQ (Discrete.natIso fun j ↦ (hiso j.as).some)).symm
  exact TStructure.t.isGE_of_iso e a

end Unbounded

namespace Plus

section Coproducts

variable {I : Type w} {a : ℤ}

/-- The direct sum in `D(A)` of a diagram of shape `Discrete I` in `D⁺(A)` whose objects are
all `≥ a` lies in `D⁺(A)`, so the inclusion creates the direct sum. -/
@[instance_reducible]
noncomputable def createsColimitι_of_isGE {F : Discrete I ⥤ Plus A}
    (hF : ∀ j, (F.obj j).IsGE a) : CreatesColimit F (Plus.ι (C := A)) :=
  createsColimitFullSubcategoryInclusion F
    ⟨a, isGE_of_isColimit_discrete
      (fun j ↦ (isGE_ι_obj_iff (F.obj j) a).2 (hF j)) (colimit.isColimit _)⟩

/-- **A family in `D⁺(A)` admitting a common lower bound has a direct sum.**  No such statement
holds without a common lower bound: see the module docstring. -/
lemma hasColimit_of_isGE {F : Discrete I ⥤ Plus A} (hF : ∀ j, (F.obj j).IsGE a) :
    HasColimit F :=
  have := createsColimitι_of_isGE hF
  hasColimit_of_created F Plus.ι

/-- **The direct sum in `D⁺(A)` of a family admitting a common lower bound is computed in
`D(A)`**: the inclusion `D⁺(A) ⥤ D(A)` preserves it. -/
lemma preservesColimit_ι_of_isGE {F : Discrete I ⥤ Plus A} (hF : ∀ j, (F.obj j).IsGE a) :
    PreservesColimit F (Plus.ι (C := A)) :=
  have := createsColimitι_of_isGE hF
  preservesColimit_of_createsColimit_and_hasColimit F Plus.ι

/-- `HasCoproductsOfShape I` for the full subcategory of objects `≥ a`, phrased for an explicit
family rather than a diagram. -/
lemma hasCoproduct_of_isGE (L : I → Plus A) (a : ℤ) (hL : ∀ i, (L i).IsGE a) :
    HasCoproduct L :=
  hasColimit_of_isGE (a := a) (fun j ↦ hL j.as)

end Coproducts

section TermwiseDirectSum

variable {I : Type w}

/-- The object of `D⁺(A)` represented by a cochain complex whose cohomology vanishes below
degree `a`. -/
noncomputable def ofIsGE (K : CochainComplex A ℤ) (a : ℤ) [K.IsGE a] : Plus A :=
  ⟨DerivedCategory.Q.obj K, a, inferInstance⟩

omit [IsGrothendieckAbelian.{w} A] in
/-- The underlying object of `D(A)` of `ofIsGE K a` is `Q.obj K`. -/
@[simp]
lemma ofIsGE_obj (K : CochainComplex A ℤ) (a : ℤ) [K.IsGE a] :
    (ofIsGE K a).obj = DerivedCategory.Q.obj K := rfl

omit [IsGrothendieckAbelian.{w} A] in
/-- An object placed in `D⁺(A)` by `ofIsGE` is bounded below by `a`. -/
lemma isGE_ofIsGE (K : CochainComplex A ℤ) (a : ℤ) [K.IsGE a] : (ofIsGE K a).IsGE a := by
  rw [← isGE_ι_obj_iff]
  exact (inferInstance : (DerivedCategory.Q.obj K).IsGE a)

/-- The cofan in `D⁺(A)` whose point is the image of the termwise direct sum `∐ M` of a family
of complexes that are all strictly `≥ a`, and whose legs are the images of the canonical
inclusions `Sigma.ι M i`. -/
noncomputable def termwiseDirectSumCofan (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] : Cofan (fun i ↦ ofIsGE (M i) a) :=
  have : (∐ M).IsStrictlyGE a := CochainComplex.isStrictlyGE_coproduct M a
  Cofan.mk (ofIsGE (∐ M) a)
    (fun i ↦ ObjectProperty.homMk (DerivedCategory.Q.map (Sigma.ι M i)))

/-- The point of `termwiseDirectSumCofan M a` has underlying object `Q.obj (∐ M)` in `D(A)`. -/
@[simp]
lemma termwiseDirectSumCofan_pt_obj (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] :
    (termwiseDirectSumCofan M a).pt.obj = DerivedCategory.Q.obj (∐ M) := rfl

/-- The `i`-th leg of `termwiseDirectSumCofan M a` has underlying morphism
`Q.map (Sigma.ι M i)`. -/
@[simp]
lemma termwiseDirectSumCofan_inj_hom (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] (i : I) :
    ((termwiseDirectSumCofan M a).inj i).hom = DerivedCategory.Q.map (Sigma.ι M i) := rfl

/-- **The termwise direct sum computes the direct sum in `D⁺(A)`.**  For a family of cochain
complexes `M` that are all strictly `≥ a`, the image under `Q` of the termwise direct sum
`∐ M`, with the images of the canonical inclusions as legs, is a direct sum in `D⁺(A)` of the
objects the `M i` represent.

This is the bounded below analogue of Tag 0A5L. -/
noncomputable def isColimitTermwiseDirectSumCofan (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] :
    IsColimit (termwiseDirectSumCofan M a) :=
  isColimitOfReflects (Plus.ι (C := A))
    ((isColimitMapCoconeCofanMkEquiv Plus.ι (fun i ↦ ofIsGE (M i) a) _).symm
      (isColimitMapCoconeCofanMkEquiv DerivedCategory.Q M (Sigma.ι M)
        (isColimitOfPreserves _ (coproductIsCoproduct M))))

end TermwiseDirectSum

section StrictModel

/-- A cochain complex that is **strictly** `≥ a` and represents a given object `X` of `D⁺(A)`
that is `≥ a`, chosen via `DerivedCategory.exists_iso_Q_obj_of_isGE`. -/
noncomputable def strictModel (X : Plus A) (a : ℤ) [X.IsGE a] : CochainComplex A ℤ :=
  have : X.obj.IsGE a := (isGE_ι_obj_iff X a).2 inferInstance
  (X.obj.exists_iso_Q_obj_of_isGE a).choose

/-- The complex `strictModel X a` is strictly `≥ a`. -/
instance isStrictlyGE_strictModel (X : Plus A) (a : ℤ) [X.IsGE a] :
    (strictModel X a).IsStrictlyGE a :=
  have : X.obj.IsGE a := (isGE_ι_obj_iff X a).2 inferInstance
  (X.obj.exists_iso_Q_obj_of_isGE a).choose_spec.choose

/-- **Every object of `D⁺(A)` that is `≥ a` is represented by a cochain complex that is
strictly `≥ a`**: `X` is isomorphic to `ofIsGE (strictModel X a) a`. -/
noncomputable def isoStrictModel (X : Plus A) (a : ℤ) [X.IsGE a] :
    X ≅ ofIsGE (strictModel X a) a :=
  have : X.obj.IsGE a := (isGE_ι_obj_iff X a).2 inferInstance
  ObjectProperty.isoMk _ (X.obj.exists_iso_Q_obj_of_isGE a).choose_spec.choose_spec.some

omit [IsGrothendieckAbelian.{w} A] in
/-- The existential reading of `isoStrictModel`, for citation.  Prefer `strictModel`,
`isStrictlyGE_strictModel` and `isoStrictModel`, which give the same content as data. -/
lemma exists_iso_ofIsGE (X : Plus A) (a : ℤ) [X.IsGE a] :
    ∃ (M : CochainComplex A ℤ) (_ : M.IsStrictlyGE a), Nonempty (X ≅ ofIsGE M a) :=
  ⟨strictModel X a, inferInstance, ⟨isoStrictModel X a⟩⟩

end StrictModel

section Transfer

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory B]
variable {I : Type w} {a : ℤ}

/-- **Transfer of a direct sum statement from `D(A)` to `D⁺(A)`.**  Let `G : D⁺(A) ⥤ D⁺(B)` be
induced by `G' : D(A) ⥤ D(B)`, in the sense that `Plus.ι ⋙ G' ≅ G ⋙ Plus.ι`.  If `G'`
commutes with the direct sum of a diagram of shape `Discrete I` in `D⁺(A)` whose objects admit
a common lower bound `a`, then so does `G`.

Both inclusions are used: the one on `A` to know that the direct sum in `D⁺(A)` is computed in
`D(A)`, and the one on `B`, which is fully faithful and therefore reflects colimits, to read
the conclusion back in `D⁺(B)`.  No bound on `B` is required. -/
lemma preservesColimit_of_preservesColimit_ι {F : Discrete I ⥤ Plus A}
    (hF : ∀ j, (F.obj j).IsGE a) (G : Plus A ⥤ Plus B)
    (G' : DerivedCategory A ⥤ DerivedCategory B) (e : Plus.ι ⋙ G' ≅ G ⋙ Plus.ι)
    (hG' : PreservesColimit (F ⋙ Plus.ι) G') : PreservesColimit F G :=
  have := preservesColimit_ι_of_isGE hF
  have := hG'
  have : PreservesColimit F (Plus.ι ⋙ G') := comp_preservesColimit Plus.ι G'
  have : PreservesColimit F (G ⋙ Plus.ι) := preservesColimit_of_natIso F e
  preservesColimit_of_reflects_of_preserves (F := G) (G := Plus.ι)

/-- **The form a consumer needs**: a functor `G : D⁺(A) ⥤ D⁺(B)` induced by a functor
`G' : D(A) ⥤ D(B)` that commutes with `I`-indexed direct sums commutes with the direct sum of
any family `L : I → D⁺(A)` admitting a common lower bound `a`. -/
lemma preservesColimit_discrete_functor_of_unbounded (L : I → Plus A) (a : ℤ)
    (hL : ∀ i, (L i).IsGE a) (G : Plus A ⥤ Plus B)
    (G' : DerivedCategory A ⥤ DerivedCategory B) (e : Plus.ι ⋙ G' ≅ G ⋙ Plus.ι)
    (hG' : PreservesColimitsOfShape (Discrete I) G') :
    PreservesColimit (Discrete.functor L) G :=
  have := hG'
  preservesColimit_of_preservesColimit_ι (a := a) (fun j ↦ hL j.as) G G' e inferInstance

/-- **Checking preservation on the termwise direct sum.**  A functor `G : D⁺(A) ⥤ D⁺(B)`
commutes with the direct sum of the family represented by cochain complexes `M i` that are all
strictly `≥ a` as soon as it sends the cofan of the termwise direct sum `∐ M` to a colimit
cofan.  This is the route available to a functor with no unbounded model, such as a right
derived functor `Functor.rightDerivedFunctorPlus`. -/
lemma preservesColimit_termwiseDirectSum (M : I → CochainComplex A ℤ) (a : ℤ)
    [∀ i, (M i).IsStrictlyGE a] (G : Plus A ⥤ Plus B)
    (h : IsColimit (G.mapCocone (termwiseDirectSumCofan M a))) :
    PreservesColimit (Discrete.functor (fun i ↦ ofIsGE (M i) a)) G :=
  preservesColimit_of_preserves_colimit_cocone (isColimitTermwiseDirectSumCofan M a) h

/-- **Checking preservation on the termwise direct sum suffices for an arbitrary family.**  If
`G : D⁺(A) ⥤ D⁺(B)` sends the cofan of the termwise direct sum `∐ M` to a colimit cofan for
*every* family `M` of cochain complexes that are all strictly `≥ a`, then `G` commutes with the
direct sum of *any* family `L : I → D⁺(A)` admitting the common lower bound `a`.

Each `L i` is replaced by `ofIsGE (strictModel (L i) a) a` along `isoStrictModel`, which is
where strict boundedness below is produced; `preservesColimit_termwiseDirectSum` applies to the
replacement, and the conclusion is transported back along the isomorphisms.  The hypothesis and
the conclusion are the two shapes in which a consumer meets this statement, so this is the
bridge between them. -/
lemma preservesColimit_discrete_of_termwiseDirectSum (a : ℤ) (G : Plus A ⥤ Plus B)
    (h : ∀ (M : I → CochainComplex A ℤ) [∀ i, (M i).IsStrictlyGE a],
      IsColimit (G.mapCocone (termwiseDirectSumCofan M a)))
    (L : I → Plus A) (hL : ∀ i, (L i).IsGE a) :
    PreservesColimit (Discrete.functor L) G :=
  have := hL
  have := preservesColimit_termwiseDirectSum (fun i ↦ strictModel (L i) a) a G
    (h fun i ↦ strictModel (L i) a)
  preservesColimit_of_iso_diagram
    (K₁ := Discrete.functor fun i ↦ ofIsGE (strictModel (L i) a) a) G
    (Discrete.natIso fun j ↦ (isoStrictModel (L j.as) a).symm)

end Transfer

section TransferBack

variable {B : Type u'} [Category.{v'} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
  [HasDerivedCategory B]
variable {I : Type w} {a b : ℤ}

/-- **Transfer of a direct sum statement from `D⁺(A)` to `D(A)`**, the converse direction of
`preservesColimit_of_preservesColimit_ι`.  Here a common lower bound is needed on both sides:
`a` for the diagram, so that its direct sum in `D⁺(A)` is computed in `D(A)`, and `b` for its
image under `G`, so that the same holds in `D⁺(B)`. -/
lemma preservesColimit_ι_of_preservesColimit {F : Discrete I ⥤ Plus A}
    (hF : ∀ j, (F.obj j).IsGE a) (G : Plus A ⥤ Plus B)
    (hG : ∀ j, (G.obj (F.obj j)).IsGE b)
    (G' : DerivedCategory A ⥤ DerivedCategory B) (e : Plus.ι ⋙ G' ≅ G ⋙ Plus.ι)
    (hGc : PreservesColimit F G) : PreservesColimit (F ⋙ Plus.ι) G' := by
  have := hasColimit_of_isGE hF
  have hιA := preservesColimit_ι_of_isGE hF
  have := preservesColimit_ι_of_isGE (F := F ⋙ G) (a := b) hG
  have := hGc
  have : PreservesColimit F (G ⋙ Plus.ι) := comp_preservesColimit G Plus.ι
  have : PreservesColimit F (Plus.ι ⋙ G') := preservesColimit_of_natIso F e.symm
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves Plus.ι (colimit.isColimit F))
    (isColimitOfPreserves (Plus.ι ⋙ G') (colimit.isColimit F))

end TransferBack

end Plus

end DerivedCategory
