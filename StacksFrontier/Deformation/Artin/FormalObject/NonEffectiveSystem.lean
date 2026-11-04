module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionGerbe
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# A system of objects of a classifying stack which is not effective

Let `A` be a commutative algebra over a commutative ring `k` and let `I ⊆ A` be an ideal. The
quotients `A ⧸ I ^ (n + 1)` form an inverse system of `k`-algebras indexed by `ℕᵒᵖ`. Its
transition maps are surjective, being quotient maps, and their kernels are locally nilpotent: a
kernel element is represented by a member of a power of `I`, and a high enough power of that
member already lies in the smaller power.

For `A = k[x, y]` and `I = (xy(x + y - 1))` the closed subscheme `V(I)` is three copies of the
affine line glued into a triangle at three points, and `Spec (A ⧸ I ^ (n + 1))` is its `n`-th
thickening. This inverse system, together with its limit, is the base of the non-effective
system of objects of the classifying stack of an abelian variety in Section 110.75 of the
source.

Over that base the source produces a system of objects of `𝒳 = [Spec(k)/A]`, for `A` an abelian
variety over an algebraically closed field `k` which is not the algebraic closure of a finite
field, which is not effective in the sense of Tag 0CXT. The reason is a comparison of torsion:
the objects of `𝒳` over a base are the `A`-torsors on it, every `A`-torsor on the limit is
torsion, and the torsor on the triangle built by glueing along translation by a non-torsion
rational point of `A` is not. A morphism in `𝒳` from the triangle level to an object over the
limit would exhibit the first class as the image of the second under a homomorphism of abelian
groups, so there is none, and the system does not descend.

## Main definitions

* `Deformation.Artin.powQuotientDiagram` — the inverse system `n ↦ A ⧸ I ^ (n + 1)` of
  `k`-algebras.
* `Deformation.Artin.trianglePolynomial` and `Deformation.Artin.triangleIdeal` — the polynomial
  `xy(x + y - 1)` in two variables and the ideal it generates.
* `Deformation.Artin.triangleThickenings` — the inverse system of the thickenings of the
  triangle.
* `Deformation.Artin.fppfOverField` and `Deformation.Artin.schemeOverField` — the big fppf site
  over `Spec k` and the scheme underlying one of its objects.
* `Deformation.Artin.fieldAsAlgebraicSpace` — `Spec k` itself, as an algebraic space over
  `Spec k`; the quotient of it by a group algebraic space `A` is the classifying stack of `A`.

## Main results

* `Deformation.Artin.locallyNilpotent_ker_factor_pow` — the kernel of `A ⧸ I ^ b → A ⧸ I ^ a` is
  locally nilpotent as soon as `a ≠ 0`.
* `Deformation.Artin.surjective_powQuotientDiagram_map` and
  `Deformation.Artin.locallyNilpotent_ker_powQuotientDiagram_map` — the two conditions imposed
  on the base of a formally effective system.
* `Deformation.Artin.triangleIdeal_ne_top` — the triangle ideal is proper, so every level of
  the system is a nonzero ring.
* `Deformation.Artin.exists_locallyNilpotentSystem_triangle` — the inverse system with its limit
  cone, surjectivity, local nilpotence and nontriviality assembled into one existence
  statement.
* `Deformation.Artin.not_isEffectiveSystem_of_not_isOfFinAddOrder` — the engine: a system of
  objects whose class at one level is not torsion, over a base whose objects all have torsion
  class, is not effective.
* `Deformation.Artin.exists_nonEffectiveSystem_quotientStack_trivialAction` — **Tag 0CXX**:
  the inverse system, the system of objects of `[Spec(k)/A]` over it, and its non-effectivity.
* `Deformation.Artin.not_isStronglyFormallyEffective_quotientStack_trivialAction` — the same
  conclusion packaged as the failure of `Deformation.Artin.IsStronglyFormallyEffective` for
  `[Spec(k)/A]`, which is the assertion the section of the source is named for.

## Implementation notes

The index category is `ℕᵒᵖ`, as in `Deformation.Artin.IsStronglyFormallyEffective`, and the
exponent is shifted by one so that the initial level `A ⧸ I` is the reduced thickening `V(I)`
itself rather than the zero ring. Transition maps are `Ideal.Quotient.factorₐ`, whose
reflexivity and composition laws give functoriality on the nose. The limit cone is the chosen
one supplied by `HasLimits (CommAlgCat k)`; no identification of its vertex with the adic
completion is made or needed here.

`[Spec(k)/A]` is formed as `AlgebraicGeometry.Stack.quotientStack` of the action groupoid of
the trivial action of `A` on `Spec k`, in the shape
`AlgebraicGeometry.Space.ActionGroupoidConstruction` at the tensor unit of the slice, which is
the shape the library already uses for the quotient by a trivial action in
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction`. The standing data of a
quotient by a group action is Tag 04WL,
`AlgebraicGeometry.Space.GroupActionSituation`. Non-effectivity is the negation of
`Deformation.Artin.IsEffectiveSystem`, and the package of identifications that makes a system
of objects lie over the spectra of the levels of the inverse system is the one
`Deformation.Artin.IsStronglyFormallyEffective` quantifies over, so the conclusion of the main
theorem is exactly what has to be supplied to that predicate to refute it.

The system of objects is built, not assumed: starting from one object over the reduced
triangle, the lifting hypothesis and dependent choice give a sequence of objects and
comparison morphisms, `CategoryTheory.Functor.ofSequence` turns these into a functor out of
`ℕ`, and `CategoryTheory.NatTrans.ofSequence` turns the comparison isomorphisms into the
natural transformation along which the base cocone is pulled back. Non-effectivity is then
derived, and is nowhere assumed.

What is *not* proved here, and is carried instead as a named hypothesis of the two main
theorems, is each mathematical input that the library does not have:

* `h0AFB`, the lifting of an object of `𝒳` along a nilpotent thickening of the triangle. This
  is the method of Tag 0AFB, whose obstruction lies in the second cohomology group of a vector
  bundle on a curve and therefore vanishes; neither that tag nor the deformation theory behind
  it is in the library.
* `h0AF9`, the finiteness of the order of the class of every object of `𝒳` over the limit. This
  is Tag 0AF9, the injectivity of the first fppf cohomology of an abelian scheme over a
  two-dimensional regular integral Noetherian base into that of its function field, combined
  with Tag 0AFA, which *is* in the library as
  `AlgebraicGeometry.Space.fppfH1_isAddTorsion`; 0AF9 is not.
* `ξ₀` and `hnontorsion`, an object of `𝒳` over the reduced triangle whose class is not
  torsion. The source builds it by glueing trivial torsors along translation by a non-torsion
  rational point of `A`, using Tag 0AEN — in the library as
  `AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant` — to see that the glued torsor
  has infinite order. The non-torsion rational point itself exists because `k` is algebraically
  closed and not the algebraic closure of a finite field, which the source flags as "actually
  not trivial to prove"; that is the one input with no tag at all.
* `H`, `cls` and `hcls`, the first cohomology class of an object of `𝒳` and its compatibility
  with restriction. This is the description of the fibre categories of a classifying stack as
  groupoids of torsors, together with the classification of torsors by first cohomology.
* `U`, `cU`, `e`, `eL`, `he`, `heL` and `hchart`, the spectra of the levels of the inverse
  system and of its limit as objects of the chosen big fppf site. This is a condition on the
  site rather than a missing theorem, and it is the same package of identifications that
  `Deformation.Artin.IsStronglyFormallyEffective` demands.

The hypothesis that `k` is not the algebraic closure of a finite field is spelled as: `k` is
not algebraic over any finite subfield of itself. It is not used, since the non-torsion point
it is there to produce is itself a hypothesis; it is kept so that the statement carries the
hypotheses the source states.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04WL](https://stacks.math.columbia.edu/tag/04WL)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u

section

variable {A : Type u} [CommRing A]

/-- The kernel of the quotient map `A ⧸ I ^ b → A ⧸ I ^ a` is locally nilpotent once `a ≠ 0`:
an element of it is represented by a member `c` of `I ^ a`, and then `c ^ b` lies in
`I ^ (a * b) ⊆ I ^ b`. -/
public theorem locallyNilpotent_ker_factor_pow {I : Ideal A} {a b : ℕ} (ha : a ≠ 0)
    (h : I ^ b ≤ I ^ a) : (RingHom.ker (Ideal.Quotient.factor h)).LocallyNilpotent := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hc : c ∈ I ^ a := by
    have hmem := RingHom.mem_ker.mp hx
    rwa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hmem
  refine ⟨b, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : c ^ b ∈ (I ^ a) ^ b := Ideal.pow_mem_pow hc _
  rw [← pow_mul] at h1
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ha)) h1

variable (k : Type u) [CommRing k] [Algebra k A]

/-- The inverse system of `k`-algebras `n ↦ A ⧸ I ^ (n + 1)`, with the quotient maps as its
transition morphisms. Its initial level is the quotient `A ⧸ I` itself. -/
public noncomputable def powQuotientDiagram (I : Ideal A) : ℕᵒᵖ ⥤ CommAlgCat.{u} k where
  obj n := .of k (A ⧸ I ^ (n.unop + 1))
  map {_ _} f := CommAlgCat.ofHom
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))))
  map_id _ := by apply CommAlgCat.hom_ext; simp
  map_comp _ _ := by apply CommAlgCat.hom_ext; simp

/-- The transition maps of the system of powers go between nested powers of the ideal. -/
private theorem pow_le_pow_of_hom {I : Ideal A} {m n : ℕᵒᵖ} (f : m ⟶ n) :
    I ^ (m.unop + 1) ≤ I ^ (n.unop + 1) :=
  Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))

/-- Every transition map of the system of powers is surjective. -/
public theorem surjective_powQuotientDiagram_map (I : Ideal A) {m n : ℕᵒᵖ} (f : m ⟶ n) :
    Function.Surjective ((powQuotientDiagram k I).map f).hom :=
  Ideal.Quotient.factor_surjective (pow_le_pow_of_hom f)

/-- Every transition map of the system of powers has locally nilpotent kernel. -/
public theorem locallyNilpotent_ker_powQuotientDiagram_map (I : Ideal A) {m n : ℕᵒᵖ}
    (f : m ⟶ n) :
    (RingHom.ker ((powQuotientDiagram k I).map f).hom.toRingHom).LocallyNilpotent :=
  locallyNilpotent_ker_factor_pow (Nat.succ_ne_zero _) (pow_le_pow_of_hom f)

/-- Every level of the system of powers of a proper ideal is a nonzero ring. -/
public theorem nontrivial_powQuotientDiagram_obj {I : Ideal A} (hI : I ≠ ⊤) (n : ℕᵒᵖ) :
    Nontrivial ((powQuotientDiagram k I).obj n) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h =>
    hI (top_le_iff.mp (h.ge.trans (Ideal.pow_le_self (Nat.succ_ne_zero _))))

end

section Triangle

variable (k : Type u) [CommRing k]

/-- The polynomial `xy(x + y - 1)` in two variables, whose zero locus is three copies of the
affine line glued into a triangle at the three points where two of the factors vanish. -/
public noncomputable def trianglePolynomial : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1 - 1)

/-- The ideal of the triangle of three affine lines, generated by `xy(x + y - 1)`. -/
public noncomputable def triangleIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {trianglePolynomial k}

/-- The triangle polynomial vanishes at the origin, which is one of the three nodes. -/
public theorem eval_zero_trianglePolynomial :
    MvPolynomial.eval (fun _ => (0 : k)) (trianglePolynomial k) = 0 := by
  simp [trianglePolynomial]

/-- The triangle ideal is proper: its generator vanishes at the origin, so it is not a unit. -/
public theorem triangleIdeal_ne_top [Nontrivial k] : triangleIdeal k ≠ ⊤ := by
  rw [triangleIdeal, Ne, Ideal.span_singleton_eq_top]
  intro h
  have hunit := h.map (MvPolynomial.eval fun _ => (0 : k))
  rw [eval_zero_trianglePolynomial] at hunit
  exact not_isUnit_zero hunit

/-- The inverse system of thickenings of the triangle of three affine lines: the `n`-th level is
`k[x, y] ⧸ (xy(x + y - 1)) ^ (n + 1)`. -/
public noncomputable abbrev triangleThickenings : ℕᵒᵖ ⥤ CommAlgCat.{u} k :=
  powQuotientDiagram k (triangleIdeal k)

/-- There is an inverse system of nonzero `k`-algebras with a limit, whose transition maps are
surjective with locally nilpotent kernels: the thickenings of the triangle of three affine
lines. These are the first two of the three conjuncts of Tag 0CXX. -/
public theorem exists_locallyNilpotentSystem_triangle [Nontrivial k] :
    ∃ (R : ℕᵒᵖ ⥤ CommAlgCat.{u} k) (c : Cone R), Nonempty (IsLimit c) ∧
      (∀ {m n : ℕᵒᵖ} (f : m ⟶ n), Function.Surjective (R.map f).hom) ∧
      (∀ {m n : ℕᵒᵖ} (f : m ⟶ n),
        (RingHom.ker (R.map f).hom.toRingHom).LocallyNilpotent) ∧
      ∀ n : ℕᵒᵖ, Nontrivial (R.obj n) :=
  ⟨triangleThickenings k, limit.cone _, ⟨limit.isLimit _⟩,
    fun f => surjective_powQuotientDiagram_map k _ f,
    fun f => locallyNilpotent_ker_powQuotientDiagram_map k _ f,
    nontrivial_powQuotientDiagram_obj k (triangleIdeal_ne_top k)⟩

end Triangle

section Classifying

open AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u₁ u₂ u₃ v₁ v₂ v₃ w

/-! ### The torsion comparison which forbids effectivity -/

/-- A system of objects is not effective over a base cocone as soon as some level of it carries
a class of infinite order while every object over the vertex of the cocone carries a class of
finite order. A cocone of the system would supply an object over the vertex together with a
morphism from that level to it, and the class of the level is then the image of the class of
that object under a homomorphism of abelian groups, hence of finite order. -/
public theorem not_isEffectiveSystem_of_not_isOfFinAddOrder
    {J : Type u₁} [Category.{v₁} J] {X : Type u₂} [Category.{v₂} X]
    {D : Type u₃} [Category.{v₃} D]
    (p : X ⥤ D) (H : Dᵒᵖ ⥤ AddCommGrpCat.{w})
    (cls : (x : X) → H.obj (Opposite.op (p.obj x)))
    (hcls : ∀ {x y : X} (φ : x ⟶ y), cls x = H.map (p.map φ).op (cls y))
    (ξ : J ⥤ X) (c : Cocone (ξ ⋙ p)) (j : J)
    (htors : ∀ x : X, p.obj x = c.pt → IsOfFinAddOrder (cls x))
    (hfree : ¬ IsOfFinAddOrder (cls (ξ.obj j))) :
    ¬ IsEffectiveSystem p ξ c := by
  rintro ⟨d, hd⟩
  have hpt : p.obj d.pt = c.pt := congrArg Cocone.pt hd
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (htors d.pt hpt)
  refine hfree (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩)
  rw [hcls (d.ι.app j), ← map_nsmul]
  simp only [Functor.const_obj_obj]
  rw [hnx, map_zero]

/-! ### The classifying stack of a group algebraic space over a field -/

variable (k : Type u) [Field k] (C : BigFppfSite.{u})
  (hk : C.Contains (Spec (CommRingCat.of k)))

/-- The big fppf site over `Spec k`. -/
public noncomputable abbrev fppfOverField := BigFppfOver C (Spec (CommRingCat.of k)) hk

/-- The scheme underlying an object of the big fppf site over `Spec k`. -/
public noncomputable abbrev schemeOverField := BigFppfOver.toScheme C (Spec (CommRingCat.of k)) hk

/-- `Spec k` itself, as an algebraic space over `Spec k`: the terminal sheaf on the big fppf
site over `Spec k`, which is the functor of points of the identity of `Spec k`. -/
public noncomputable def fieldAsAlgebraicSpace :
    AlgebraicSpaces C (Spec (CommRingCat.of k)) hk :=
  ⟨yoneda.obj (Over.mk (𝟙 (C.obj hk))),
    isAlgebraicSpace_yoneda C (Spec (CommRingCat.of k)) hk _⟩

variable (A : Over (fieldAsAlgebraicSpace k C hk).obj) [GrpObj A]
  (hA : IsAlgebraicSpace C (Spec (CommRingCat.of k)) hk A.left)
  (Q : Space.ActionGroupoidConstruction (fieldAsAlgebraicSpace k C hk) A
    (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj)) hA (fieldAsAlgebraicSpace k C hk).property)

/-! ### A system of objects of `[Spec(k)/A]` which is not effective -/

/-- **Stacks Project, Tag 0CXX.** Let `k` be an algebraically closed field which is not the
algebraic closure of a finite field, let `A` be an abelian variety over `k` and let
`𝒳 = [Spec(k)/A]`. There is an inverse system of `k`-algebras whose transition maps are
surjective with locally nilpotent kernels — the thickenings of the triangle of three affine
lines — and a system of objects of `𝒳` over the spectra of its levels, which is not effective
in the sense of Tag 0CXT.

The mathematical inputs the library does not have are hypotheses: `h0AFB` is the lifting of an
object along a nilpotent thickening of the triangle, the method of Tag 0AFB; `h0AF9` is the
finiteness of the order of the class of every object over the limit, Tag 0AF9 together with
Tag 0AFA; `ξ₀` together with `hnontorsion` is the object over the reduced triangle whose class
has infinite order, which the source builds from a non-torsion rational point of `A` and
Tag 0AEN; `H`, `cls` and `hcls` are the first cohomology class of an object of `𝒳`, that is,
the description of the fibre categories of a classifying stack as groupoids of torsors; and
`U`, `cU`, `e`, `eL`, `he`, `heL`, `hchart` realize the spectra of the levels of the inverse
system and of its limit as objects of the chosen big fppf site. Non-effectivity is nowhere
assumed, and the system of objects is constructed rather than supposed. -/
@[stacks 0CXX "RESTRICTED: Tag 0AFB (lifting an object along a thickening) is the hypothesis \
h0AFB, Tags 0AF9 and 0AFA (finite order of the class over the limit) are h0AF9, the non-torsion \
rational point of the abelian variety with Tag 0AEN is ξ₀ with hnontorsion, and the class of a \
torsor is the data H, cls, hcls; the site realization is U, cU, e, eL, he, heL, hchart"]
public theorem exists_nonEffectiveSystem_quotientStack_trivialAction
    [IsAlgClosed k]
    (_hkinf : ∀ F : Subfield k, Finite F → ¬ Algebra.IsAlgebraic F k)
    (U : ℕ ⥤ fppfOverField k C hk) (cU : Cocone U)
    (cR : Cone (triangleThickenings k)) (hcR : IsLimit cR)
    (e : ∀ n : ℕ, (schemeOverField k C hk).obj (U.obj n) ≅
      Spec (.of ((triangleThickenings k).obj (.op n))))
    (eL : (schemeOverField k C hk).obj cU.pt ≅ Spec (.of cR.pt))
    (he : ∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k C hk).map (U.map g) ≫ (e j).hom =
      (e i).hom ≫ Scheme.Spec.map
        (CommRingCat.ofHom ((triangleThickenings k).map g.op).hom.toRingHom).op)
    (heL : ∀ n : ℕ, (schemeOverField k C hk).map (cU.ι.app n) ≫ eL.hom =
      (e n).hom ≫ Scheme.Spec.map
        (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
    (hchart : eL.inv ≫ C.inclusion.map cU.pt.hom =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cR.pt)).op)
    (H : (fppfOverField k C hk)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (cls : (x : (Stack.quotientStack Q.groupoid).obj) →
      H.obj (.op ((Stack.quotientStack Q.groupoid).p.obj x)))
    (hcls : ∀ {x y : (Stack.quotientStack Q.groupoid).obj} (φ : x ⟶ y),
      cls x = H.map ((Stack.quotientStack Q.groupoid).p.map φ).op (cls y))
    (ξ₀ : (Stack.quotientStack Q.groupoid).obj)
    (hξ₀ : (Stack.quotientStack Q.groupoid).p.obj ξ₀ ≅ U.obj 0)
    (hnontorsion : ¬ IsOfFinAddOrder (cls ξ₀))
    (h0AF9 : ∀ x : (Stack.quotientStack Q.groupoid).obj,
      (Stack.quotientStack Q.groupoid).p.obj x = cU.pt → IsOfFinAddOrder (cls x))
    (h0AFB : ∀ (n : ℕ) (x : (Stack.quotientStack Q.groupoid).obj)
      (a : (Stack.quotientStack Q.groupoid).p.obj x ≅ U.obj n),
      ∃ (y : (Stack.quotientStack Q.groupoid).obj)
        (b : (Stack.quotientStack Q.groupoid).p.obj y ≅ U.obj (n + 1))
        (φ : x ⟶ y), (Stack.quotientStack Q.groupoid).p.map φ ≫ b.hom =
          a.hom ≫ U.map (homOfLE (Nat.le_succ n))) :
    ∃ (R : ℕᵒᵖ ⥤ CommAlgCat.{u} k) (cS : Cone R)
      (ξ : ℕ ⥤ (Stack.quotientStack Q.groupoid).obj)
      (c : Cocone (ξ ⋙ (Stack.quotientStack Q.groupoid).p))
      (f : ∀ n : ℕ, (schemeOverField k C hk).obj
        ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).obj n) ≅ Spec (.of (R.obj (.op n))))
      (fL : (schemeOverField k C hk).obj c.pt ≅ Spec (.of cS.pt)),
      Nonempty (IsLimit cS) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j), Function.Surjective (R.map g).hom) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j),
        (RingHom.ker (R.map g).hom.toRingHom).LocallyNilpotent) ∧
      (∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k C hk).map
          ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).map g) ≫ (f j).hom =
        (f i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map g.op).hom.toRingHom).op) ∧
      (∀ n : ℕ, (schemeOverField k C hk).map (c.ι.app n) ≫ fL.hom =
        (f n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cS.π.app (.op n)).hom.toRingHom).op) ∧
      (fL.inv ≫ C.inclusion.map c.pt.hom =
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cS.pt)).op) ∧
      ¬ IsEffectiveSystem (Stack.quotientStack Q.groupoid).p ξ c := by
  classical
  choose Y bb pp hpp using h0AFB
  let seq : ∀ n : ℕ, Σ' x : (Stack.quotientStack Q.groupoid).obj,
      (Stack.quotientStack Q.groupoid).p.obj x ≅ U.obj n :=
    Nat.rec ⟨ξ₀, hξ₀⟩ (fun n d => ⟨Y n d.1 d.2, bb n d.1 d.2⟩)
  let xs : ℕ → (Stack.quotientStack Q.groupoid).obj := fun n => (seq n).1
  let as : ∀ n : ℕ, (Stack.quotientStack Q.groupoid).p.obj (xs n) ≅ U.obj n := fun n => (seq n).2
  let ff : ∀ n : ℕ, xs n ⟶ xs (n + 1) := fun n => pp n (xs n) (as n)
  let ξ : ℕ ⥤ (Stack.quotientStack Q.groupoid).obj := Functor.ofSequence ff
  have hsucc : ∀ n : ℕ, ξ.map (homOfLE (Nat.le_succ n)) = ff n := fun n =>
    Functor.ofSequence_map_homOfLE_succ ff n
  let α : ξ ⋙ (Stack.quotientStack Q.groupoid).p ⟶ U :=
    NatTrans.ofSequence (fun n => (as n).hom) (by
      intro n
      change (Stack.quotientStack Q.groupoid).p.map (ξ.map (homOfLE (Nat.le_succ n))) ≫
        (as (n + 1)).hom = (as n).hom ≫ U.map (homOfLE (Nat.le_succ n))
      rw [hsucc n]
      exact hpp n (xs n) (as n))
  let as' : ∀ n : ℕ, (Stack.quotientStack Q.groupoid).p.obj (ξ.obj n) ≅ U.obj n := as
  have hnat : ∀ {i j : ℕ} (g : i ⟶ j),
      (Stack.quotientStack Q.groupoid).p.map (ξ.map g) ≫ (as' j).hom =
        (as' i).hom ≫ U.map g := fun g => α.naturality g
  have hcomp1 : ∀ {i j : ℕ} (g : i ⟶ j),
      (schemeOverField k C hk).map ((Stack.quotientStack Q.groupoid).p.map (ξ.map g)) ≫
          ((schemeOverField k C hk).map (as' j).hom ≫ (e j).hom) =
        ((schemeOverField k C hk).map (as' i).hom ≫ (e i).hom) ≫
          Scheme.Spec.map (CommRingCat.ofHom
            ((triangleThickenings k).map g.op).hom.toRingHom).op := by
    intro i j g
    rw [← Category.assoc, ← Functor.map_comp, hnat g, Functor.map_comp, Category.assoc,
      he g, Category.assoc]
  have hcomp2 : ∀ n : ℕ,
      (schemeOverField k C hk).map ((as' n).hom ≫ cU.ι.app n) ≫ eL.hom =
        ((schemeOverField k C hk).map (as' n).hom ≫ (e n).hom) ≫
          Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op := by
    intro n
    rw [Functor.map_comp, Category.assoc, heL n, Category.assoc]
  refine ⟨triangleThickenings k, cR, ξ, ⟨cU.pt, α ≫ cU.ι⟩,
    fun n => (schemeOverField k C hk).mapIso (as' n) ≪≫ e n, eL, ⟨hcR⟩,
    surjective_powQuotientDiagram_map k _, locallyNilpotent_ker_powQuotientDiagram_map k _,
    hcomp1, hcomp2, hchart, ?_⟩
  refine not_isEffectiveSystem_of_not_isOfFinAddOrder _ H cls hcls ξ _ 0 ?_ hnontorsion
  exact h0AF9

/-- The classifying stack of a group algebraic space over a field does not satisfy strong
formal effectiveness, under the hypotheses of
`Deformation.Artin.exists_nonEffectiveSystem_quotientStack_trivialAction`. This is the
assertion that the section of the source containing Tag 0CXX is named for; it is that theorem
with its conclusion fed back to `Deformation.Artin.IsStronglyFormallyEffective`, whose chart is
taken to be the identity of `Spec k`. -/
public theorem not_isStronglyFormallyEffective_quotientStack_trivialAction
    [IsAlgClosed k]
    (hkinf : ∀ F : Subfield k, Finite F → ¬ Algebra.IsAlgebraic F k)
    (U : ℕ ⥤ fppfOverField k C hk) (cU : Cocone U)
    (cR : Cone (triangleThickenings k)) (hcR : IsLimit cR)
    (e : ∀ n : ℕ, (schemeOverField k C hk).obj (U.obj n) ≅
      Spec (.of ((triangleThickenings k).obj (.op n))))
    (eL : (schemeOverField k C hk).obj cU.pt ≅ Spec (.of cR.pt))
    (he : ∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k C hk).map (U.map g) ≫ (e j).hom =
      (e i).hom ≫ Scheme.Spec.map
        (CommRingCat.ofHom ((triangleThickenings k).map g.op).hom.toRingHom).op)
    (heL : ∀ n : ℕ, (schemeOverField k C hk).map (cU.ι.app n) ≫ eL.hom =
      (e n).hom ≫ Scheme.Spec.map
        (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
    (hchart : eL.inv ≫ C.inclusion.map cU.pt.hom =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cR.pt)).op)
    (H : (fppfOverField k C hk)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (cls : (x : (Stack.quotientStack Q.groupoid).obj) →
      H.obj (.op ((Stack.quotientStack Q.groupoid).p.obj x)))
    (hcls : ∀ {x y : (Stack.quotientStack Q.groupoid).obj} (φ : x ⟶ y),
      cls x = H.map ((Stack.quotientStack Q.groupoid).p.map φ).op (cls y))
    (ξ₀ : (Stack.quotientStack Q.groupoid).obj)
    (hξ₀ : (Stack.quotientStack Q.groupoid).p.obj ξ₀ ≅ U.obj 0)
    (hnontorsion : ¬ IsOfFinAddOrder (cls ξ₀))
    (h0AF9 : ∀ x : (Stack.quotientStack Q.groupoid).obj,
      (Stack.quotientStack Q.groupoid).p.obj x = cU.pt → IsOfFinAddOrder (cls x))
    (h0AFB : ∀ (n : ℕ) (x : (Stack.quotientStack Q.groupoid).obj)
      (a : (Stack.quotientStack Q.groupoid).p.obj x ≅ U.obj n),
      ∃ (y : (Stack.quotientStack Q.groupoid).obj)
        (b : (Stack.quotientStack Q.groupoid).p.obj y ≅ U.obj (n + 1))
        (φ : x ⟶ y), (Stack.quotientStack Q.groupoid).p.map φ ≫ b.hom =
          a.hom ≫ U.map (homOfLE (Nat.le_succ n))) :
    ¬ IsStronglyFormallyEffective C (Spec (CommRingCat.of k)) hk
      (Stack.quotientStack Q.groupoid).p
      (Stack.isFiberedInGroupoids_quotientStack Q.groupoid) := by
  obtain ⟨R, cS, ξ, c, f, fL, ⟨hlim⟩, hsurj, hnil, h1, h2, h3, hne⟩ :=
    exists_nonEffectiveSystem_quotientStack_trivialAction k C hk A hA Q hkinf U cU cR hcR e eL
      he heL hchart H cls hcls ξ₀ hξ₀ hnontorsion h0AF9 h0AFB
  intro hSFE
  exact hne (hSFE k (𝟙 (Spec (CommRingCat.of k))) R cS hlim hsurj hnil ξ c f fL
    (fun g => h1 g) h2 (h3.trans (Category.comp_id _).symm))

end Classifying

end Deformation.Artin
