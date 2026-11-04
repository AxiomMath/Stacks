module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantExtensions
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant cohomology of a derived tensor product, bounded above

Let `(C, J)` be a site and `Λ` a Noetherian commutative ring. Stacks Tag 094H asserts that for
`K, L` in `D^-(C, Λ)` whose cohomology sheaves are locally constant sheaves of `Λ`-modules of
finite type, the cohomology sheaves of `K ⊗^L_Λ L` are again locally constant of finite type.

The source's proof has two halves. The first is a reduction: `H^i(K ⊗^L L)` is computed by the
truncations `τ^{≥ i-1}K` and `τ^{≥ i-1}L`, which are bounded, so it suffices to treat bounded
`K` and `L`. The second half treats the bounded case by invoking Tag 094G to replace `K` and
`L`, locally on the site, by bounded complexes of locally constant sheaves of finite type, then
by bounded above complexes of finite free `Λ`-modules, for which the derived tensor product is
the ordinary total tensor product and the conclusion is termwise.

This file proves the **first half in full**, and the **termwise statement** which is what the
second half needs once the complexes have been produced. It does not produce them; see
"What is not proved".

## Main results

* `Stacks.ConstantSheaf.prop_homology_of_isLE_add`: **the reduction of Tag 094H to its bounded
  case**, for an arbitrary bifunctor on a derived category which is exact in each variable and
  carries bounds to their sum. Stated for an arbitrary property of objects closed under
  isomorphism and containing zero.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_of_bounded`:
  **Tag 094H, the reduction of the bounded above case to the bounded case**, the previous result
  at the locally constant finite type property of Tag 093U.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_mapBifunctor`: **Tag 094H, the
  termwise conclusion** — each term of the total tensor complex of two bounded above complexes
  of locally constant sheaves of finite type is locally constant of finite type.

## Implementation notes

The reduction is stated for an abstract bifunctor `T` on `D(A)` because nothing about the
derived tensor product enters it beyond exactness in each variable and the estimate
`K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b)`. Both are fields (or immediate
consequences of fields) of the derived tensor product data of Tag 06YU, and keeping them as
hypotheses means this half of Tag 094H is independent of which construction of the derived
tensor product a client uses, and of the category in which the sheaves of `Λ`-modules are
modelled.

The reduction itself replaces `K` by `τ^{> i-b-1}K` and `L` by `τ^{> i-a-1}L`, where `a` and `b`
bound `K` and `L` above. Each replacement sits in a distinguished triangle whose remaining
vertex is `τ^{≤ ·}` of the original, and the boundedness estimate puts
`T(τ^{≤ i-b-1}K, L)` and `T(τ^{> i-b-1}K, τ^{≤ i-a-1}L)` in degrees `≤ i - 1`; so `H^i` of the
second map of each triangle is both mono and epi, by the long exact sequence of a distinguished
triangle, and therefore invertible. Truncation preserves the property of all cohomology sheaves
by the same argument applied to the truncation triangle.

The termwise statement is the decomposition of the degree `n` term of a total complex as the
coproduct of the `T(P^p, Q^q)` with `p + q = n`. Two strict bounds above make the set of
contributing `p` finite — it is `Finset.Icc (n - b) a` — and the complementary summands are
zero, so the inclusions of the contributing summands are already a colimit cofan. The property
is then read off from closure under finite coproducts, which a weak Serre class has: it contains
zero, is closed under isomorphism, and contains biproducts of its objects, so
`ObjectProperty.IsClosedUnderFiniteCoproducts` follows from `ObjectProperty.prop_biprod`.

The descent datum of the cofan is a map out of `T(P^p, Q^q)` for each `p + q = n`, while the
cofan is indexed by `p` alone with second index `n - p`, so the datum transports along
`q = n - p`. The transport is an `eqToHom` inside the proof of a `Prop` and never enters a
definition: substituting the equality instead, which would avoid it, leaves the descent map
behind an `Eq.ndrec` that `HomologicalComplex.ι_mapBifunctorDesc` cannot rewrite under.

The module universe is `max u v w` and the coefficient ring is taken in `Type (max u v w)`, as
in `StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorFiniteType`: the monoidal structure
on `ModuleCat.{s} Λ` requires `Λ : Type s`, and that choice keeps `u`, `v`, `w` free while
making every sheafification hypothesis automatic.

## What is not proved

The **bounded case** of Tag 094H is not proved, so Tag 094H is not proved. What is missing is
exactly the production of the two complexes the termwise statement consumes, and it needs two
inputs this file does not have.

The general case of Tag 094G, the induction on the number of nonzero cohomology sheaves, is
**not among them**: it is formalized as
`Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex_of_isGE_of_isLE` in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexInduction`, of which
`Stacks.ConstantSheaf.exists_cover_isRepresentedByLocallyConstantComplex` is the base case.

* A replacement of a bounded complex of finitely generated `Λ`-modules by a bounded above
  complex of finite free ones. Over a Noetherian `Λ` this exists, degreewise, because the
  kernels stay finitely generated, and the constant sheaf on a free module is flat, so the
  resulting complex of constant sheaves is K-flat and computes the derived tensor product. None
  of that is formalized here.
* Compatibility of the derived tensor product with restriction to a slice site. Tag 094G's
  conclusion is a statement about the restrictions of `K` and `L` to the members of a covering
  family, so the derived tensor product of the restrictions must be the restriction of the
  derived tensor product before
  `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_local` can assemble the
  conclusion. Restriction to a slice site is exact and monoidal, so this is expected, but it is
  a property of the chosen derived tensor product and is not among the hypotheses carried here.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.ConstantSheaf

universe w v u

/-! ### Truncation and the long exact sequence -/

section Truncation

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- If the first vertex of a distinguished triangle is in degrees `≤ a` then the second map of
the triangle is an isomorphism on `H^n` for every `n > a`: the long exact sequence of the
triangle has zeros on both sides of that map. -/
public theorem isIso_homologyMap_mor₂_of_isLE {T : Triangle (DerivedCategory A)}
    (hT : T ∈ distTriang (DerivedCategory A)) (a n : ℤ) (hLE : T.obj₁.IsLE a) (hn : a < n) :
    IsIso ((DerivedCategory.homologyFunctor A n).map T.mor₂) := by
  have := hLE
  have : Mono ((DerivedCategory.homologyFunctor A n).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT n]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ a n hn).eq_of_src _ _
  have : Epi ((DerivedCategory.homologyFunctor A n).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1)]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ a (n + 1) (by omega)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

/-- Truncating below preserves a property of all the cohomology objects: in degrees `≤ a` the
truncation is zero, and above `a` the truncation map is an isomorphism on cohomology. -/
theorem prop_homology_truncGT (W : ObjectProperty A) [W.ContainsZero]
    [W.IsClosedUnderIsomorphisms] (K : DerivedCategory A)
    (hK : ∀ n, W ((DerivedCategory.homologyFunctor A n).obj K)) (a n : ℤ) :
    W ((DerivedCategory.homologyFunctor A n).obj
      ((DerivedCategory.TStructure.t.truncGT a).obj K)) := by
  by_cases hn : n ≤ a
  · exact W.prop_of_isZero (DerivedCategory.isZero_of_isGE _ (a + 1) n (by omega))
  · have h : ((DerivedCategory.TStructure.t.triangleLEGT a).obj K).obj₁.IsLE a := by
      rw [Triangulated.TStructure.triangleLEGT_obj_obj₁]
      infer_instance
    have hiso := isIso_homologyMap_mor₂_of_isLE
      (DerivedCategory.TStructure.t.triangleLEGT_distinguished a K) a n h (by omega)
    rw [← Triangulated.TStructure.triangleLEGT_obj_obj₃ DerivedCategory.TStructure.t a K]
    refine W.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A n).map
      ((DerivedCategory.TStructure.t.triangleLEGT a).obj K).mor₂)) ?_
    rw [Triangulated.TStructure.triangleLEGT_obj_obj₂]
    exact hK n

/-- **The reduction of Stacks Tag 094H to its bounded case.** Let `T` be a bifunctor on `D(A)`
which is exact in each variable and which carries objects in degrees `≤ a` and `≤ b` to objects
in degrees `≤ a + b`, and let `W` be a property of objects of `A` containing zero and closed
under isomorphism. If `W` holds for every cohomology object of `(T.obj K).obj L` whenever `K`
and `L` are bounded with all cohomology objects in `W`, then the same holds for `K` and `L`
merely bounded above.

In degree `i` the two factors may be truncated to `τ^{> i-b-1}K` and `τ^{> i-a-1}L`, which are
bounded, and the boundedness estimate puts both error terms in degrees `≤ i - 1`, where they do
not contribute to `H^i`. -/
theorem prop_homology_of_isLE_add
    (T : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    [∀ L, (T.flip.obj L).CommShift ℤ] [∀ L, (T.flip.obj L).IsTriangulated]
    (W : ObjectProperty A) [W.ContainsZero] [W.IsClosedUnderIsomorphisms]
    (hbound : ∀ (K L : DerivedCategory A) (a b : ℤ), K.IsLE a → L.IsLE b →
      ((T.obj K).obj L).IsLE (a + b))
    (hbounded : ∀ (K L : DerivedCategory.Bounded A),
      (∀ i, W ((DerivedCategory.homologyFunctor A i).obj K.obj)) →
      (∀ i, W ((DerivedCategory.homologyFunctor A i).obj L.obj)) →
      ∀ i, W ((DerivedCategory.homologyFunctor A i).obj ((T.obj K.obj).obj L.obj)))
    (K L : DerivedCategory.Minus A)
    (hK : ∀ i, W ((DerivedCategory.homologyFunctor A i).obj K.obj))
    (hL : ∀ i, W ((DerivedCategory.homologyFunctor A i).obj L.obj)) :
    ∀ i, W ((DerivedCategory.homologyFunctor A i).obj ((T.obj K.obj).obj L.obj)) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  have := ha
  have := hb
  intro i
  let t := DerivedCategory.TStructure.t (C := A)
  let c := i - b - 1
  let d := i - a - 1
  let K' : DerivedCategory.Bounded A :=
    ⟨(t.truncGT c).obj K.obj, ⟨⟨c + 1, inferInstance⟩, ⟨a, inferInstance⟩⟩⟩
  let L' : DerivedCategory.Bounded A :=
    ⟨(t.truncGT d).obj L.obj, ⟨⟨d + 1, inferInstance⟩, ⟨b, inferInstance⟩⟩⟩
  let F := T.flip.obj L.obj
  let G := T.obj K'.obj
  let S := F.mapTriangle.obj ((t.triangleLEGT c).obj K.obj)
  let U := G.mapTriangle.obj ((t.triangleLEGT d).obj L.obj)
  have hS : S ∈ distTriang (DerivedCategory A) :=
    F.map_distinguished _ (t.triangleLEGT_distinguished c K.obj)
  have hU : U ∈ distTriang (DerivedCategory A) :=
    G.map_distinguished _ (t.triangleLEGT_distinguished d L.obj)
  have hS₁ : S.obj₁ = (T.obj ((t.truncLE c).obj K.obj)).obj L.obj := by
    simp only [S, F, Functor.mapTriangle_obj, Triangle.mk_obj₁,
      Triangulated.TStructure.triangleLEGT_obj_obj₁, Functor.flip_obj_obj]
  have hU₁ : U.obj₁ = (T.obj K'.obj).obj ((t.truncLE d).obj L.obj) := by
    simp only [U, G, Functor.mapTriangle_obj, Triangle.mk_obj₁,
      Triangulated.TStructure.triangleLEGT_obj_obj₁]
  have hSle : S.obj₁.IsLE (i - 1) := by
    have h := hbound ((t.truncLE c).obj K.obj) L.obj c b inferInstance hb
    rw [show c + b = i - 1 by dsimp only [c]; omega] at h
    rw [hS₁]
    exact h
  have hUle : U.obj₁.IsLE (i - 1) := by
    have h := hbound K'.obj ((t.truncLE d).obj L.obj) a d inferInstance inferInstance
    rw [show a + d = i - 1 by dsimp only [d]; omega] at h
    rw [hU₁]
    exact h
  have hiS := isIso_homologyMap_mor₂_of_isLE hS (i - 1) i hSle (by omega)
  have hiU := isIso_homologyMap_mor₂_of_isLE hU (i - 1) i hUle (by omega)
  exact W.prop_of_iso
    ((@asIso _ _ _ _ _ hiS ≪≫ @asIso _ _ _ _ _ hiU).symm)
    (hbounded K' L' (prop_homology_truncGT W K.obj hK c)
      (prop_homology_truncGT W L.obj hL d) i)

end Truncation

/-! ### Terms of a total complex -/

section TotalComplex

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Preadditive A] [Preadditive B] [Preadditive D]

/-- A weak Serre class is closed under finite coproducts: it contains zero, is closed under
isomorphism, and contains the biproduct of any two of its objects. -/
theorem isClosedUnderFiniteCoproducts_of_isWeakSerreClass {E : Type*} [Category* E] [Abelian E]
    (W : ObjectProperty E) [W.IsWeakSerreClass] : W.IsClosedUnderFiniteCoproducts := by
  have : W.IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨F, hF⟩ => W.prop_of_iso
      ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair F)).symm)
      (W.prop_biprod (hF ⟨.left⟩) (hF ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- A term `T(P^p, Q^q)` vanishes when `P^p` or `Q^q` does, by strict upper bounds. -/
private theorem isZero_obj_obj_of_isStrictlyLE (T : A ⥤ B ⥤ D) [T.Additive]
    [∀ X, (T.obj X).Additive] (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] (p q : ℤ) (h : a < p ∨ b < q) :
    IsZero ((T.obj (P.X p)).obj (Q.X q)) := by
  rcases h with h | h
  · exact (T.flip.obj (Q.X q)).map_isZero (P.isZero_of_isStrictlyLE a p h)
  · exact (T.obj (P.X p)).map_isZero (Q.isZero_of_isStrictlyLE b q h)

/-- **Each term of the total complex of a bifunctor applied to two complexes bounded strictly
above lies in any property of objects closed under finite coproducts, as soon as every
`T(P^p, Q^q)` does.** Only finitely many pairs `(p, q)` with `p + q = n` contribute, since
`P^p` vanishes for `p > a` and `Q^q` for `q > b`, so the inclusions of the contributing summands
exhibit the degree `n` term as a finite coproduct. -/
theorem prop_mapBifunctor_of_isStrictlyLE (T : A ⥤ B ⥤ D) [T.Additive] [∀ X, (T.obj X).Additive]
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor P Q T (ComplexShape.up ℤ)] (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] (W : ObjectProperty D)
    [W.IsClosedUnderFiniteCoproducts] (hW : ∀ p q, W ((T.obj (P.X p)).obj (Q.X q))) (n : ℤ) :
    W ((HomologicalComplex.mapBifunctor P Q T (ComplexShape.up ℤ)).X n) := by
  classical
  let I := {p : ℤ // p ∈ Finset.Icc (n - b) a}
  let X (p : I) := (T.obj (P.X p.val)).obj (Q.X (n - p.val))
  let S : Cofan X := Cofan.mk
    ((HomologicalComplex.mapBifunctor P Q T (ComplexShape.up ℤ)).X n)
    (fun p => HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p.val (n - p.val) n
      (by dsimp; omega))
  have hzero (p q : ℤ) (hpq : p + q = n) (hp : p ∉ Finset.Icc (n - b) a) :
      IsZero ((T.obj (P.X p)).obj (Q.X q)) := by
    refine isZero_obj_obj_of_isStrictlyLE T P Q a b p q ?_
    simp only [Finset.mem_Icc] at hp
    omega
  let φ (s : Cofan X) (p q : ℤ) (hpq : p + q = n) : (T.obj (P.X p)).obj (Q.X q) ⟶ s.pt :=
    if hp : p ∈ Finset.Icc (n - b) a then
      eqToHom (congrArg (fun q => (T.obj (P.X p)).obj (Q.X q))
        (show q = n - p by omega)) ≫ s.inj ⟨p, hp⟩
    else 0
  have hS : IsColimit S := Cofan.IsColimit.mk S
    (fun s => HomologicalComplex.mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := T) (c := .up ℤ)
      (fun p q hpq => φ s p q hpq))
    (fun s p => by
      simp only [S, cofan_mk_inj]
      rw [HomologicalComplex.ι_mapBifunctorDesc]
      simp only [φ, dite_eq_left p.2, eqToHom_refl, Category.id_comp]
      rfl)
    (fun s m hm => by
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      have hpq' : p + q = n := hpq
      by_cases hp : p ∈ Finset.Icc (n - b) a
      · obtain rfl : q = n - p := by omega
        have h := hm ⟨p, hp⟩
        simp only [S, cofan_mk_inj] at h
        rw [HomologicalComplex.ι_mapBifunctorDesc]
        simp only [φ, dite_eq_left hp, eqToHom_refl, Category.id_comp]
        exact h
      · exact (hzero p q hpq' hp).eq_of_src _ _)
  exact W.prop_of_isColimit_cofan (F := S) hS (fun p => hW p.val (n - p.val))

/-- **The total complex of a bifunctor applied to two complexes bounded strictly above is itself
bounded strictly above**, by the sum of the two bounds. Every summand `T(P^p, Q^q)` of the term
in a degree `n > a + b` has `p > a` or `q > b`, so one argument vanishes and the summand vanishes
with it.

`Stacks.DerivedTensor.RingedSite.isStrictlyLE_mapBifunctor` is this statement for the tensor
product of sheaves of modules on a ringed site; here the bifunctor is arbitrary, which is what a
total complex formed in another category needs. -/
theorem isStrictlyLE_mapBifunctor (T : A ⥤ B ⥤ D) [T.Additive] [∀ X, (T.obj X).Additive]
    (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor P Q T (ComplexShape.up ℤ)] (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE
      (HomologicalComplex.mapBifunctor P Q T (ComplexShape.up ℤ)) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpq' : p + q = n := hpq
  exact (isZero_obj_obj_of_isStrictlyLE T P Q a b p q (by omega)).eq_of_src _ _

end TotalComplex

/-! ### Tag 094H for sheaves of modules -/

section Sheaves

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v w)) [CommRing Λ]

attribute [local instance] HasDerivedCategory.standard

section Noetherian

variable [IsNoetherianRing Λ]

/-- The locally constant sheaves of `Λ`-modules of finite type are closed under finite
coproducts, being a weak Serre class by Tag 093U. -/
instance isClosedUnderFiniteCoproducts_isFiniteTypeLocallyConstantModuleSheaf :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) :=
  isClosedUnderFiniteCoproducts_of_isWeakSerreClass _

/-- **Stacks Tag 094H, the termwise conclusion.** Let `P` and `Q` be cochain complexes of
sheaves of `Λ`-modules, bounded strictly above, all of whose terms are locally constant of
finite type, and let `T` be a bifunctor on sheaves of `Λ`-modules, additive in each variable,
whose values on those terms are locally constant of finite type — for the sheafified tensor
product this is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_tensor`. Then every term of the
total complex of `T` applied to `P` and `Q` is locally constant of finite type.

This is what the bounded case of Tag 094H consumes once Tag 094G and a finite free model have
produced the two complexes: the derived tensor product of two such complexes is the class of
their total tensor complex, so its cohomology sheaves are subquotients of these terms, and the
weak Serre property of Tag 093U finishes the argument. -/
@[stacks 094H "the termwise conclusion: every term of the total complex of an additive \
  bifunctor applied to two bounded above complexes of locally constant sheaves of finite type \
  is locally constant of finite type"]
theorem isFiniteTypeLocallyConstantModuleSheaf_mapBifunctor
    (T : Sheaf J (ModuleCat.{max u v w} Λ) ⥤ Sheaf J (ModuleCat.{max u v w} Λ) ⥤
      Sheaf J (ModuleCat.{max u v w} Λ)) [T.Additive] [∀ X, (T.obj X).Additive]
    (P Q : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ)
    [HomologicalComplex.HasMapBifunctor P Q T (ComplexShape.up ℤ)] (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b]
    (hT : ∀ p q, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((T.obj (P.X p)).obj (Q.X q))) (n : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((HomologicalComplex.mapBifunctor P Q T (ComplexShape.up ℤ)).X n) :=
  prop_mapBifunctor_of_isStrictlyLE T P Q a b _ hT n

end Noetherian

/-- **Stacks Tag 094H, the reduction of the bounded above case to the bounded case.** Let `T` be
a bifunctor on the derived category of sheaves of `Λ`-modules which is exact in each variable
and carries objects in degrees `≤ a` and `≤ b` to objects in degrees `≤ a + b` — both are
properties of the derived tensor product of Tag 06YU. If the conclusion of Tag 094H holds for
bounded `K` and `L`, then it holds for `K` and `L` in `D^-`.

The proof is the first half of the source's: `H^i((T.obj K).obj L)` is computed by the bounded
truncations `τ^{> i-b-1}K` and `τ^{> i-a-1}L`. -/
@[stacks 094H "the reduction of the bounded above case to the bounded case, for a bifunctor \
  exact in each variable which carries bounds above to their sum; the bounded case is \
  a hypothesis"]
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_of_bounded
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    [∀ K, (T.obj K).CommShift ℤ] [∀ K, (T.obj K).IsTriangulated]
    [∀ L, (T.flip.obj L).CommShift ℤ] [∀ L, (T.flip.obj L).IsTriangulated]
    (hbound : ∀ (K L : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (a b : ℤ),
      K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b))
    (hbounded : ∀ (K L : DerivedCategory.Bounded (Sheaf J (ModuleCat.{max u v w} Λ))),
      (∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj K.obj)) →
      (∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj L.obj)) →
      ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj ((T.obj K.obj).obj L.obj)))
    (K L : DerivedCategory.Minus (Sheaf J (ModuleCat.{max u v w} Λ)))
    (hK : ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K.obj))
    (hL : ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj L.obj)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj ((T.obj K.obj).obj L.obj)) :=
  prop_homology_of_isLE_add T _ hbound hbounded K L hK hL i

end Sheaves

end Stacks.ConstantSheaf

end
