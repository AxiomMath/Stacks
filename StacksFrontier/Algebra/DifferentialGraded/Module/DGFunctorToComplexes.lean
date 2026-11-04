module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory

/-!
# A differential graded functor into complexes is exact on homotopy categories

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra, let `B` be an
`R`-linear preadditive category and let `F : Mod^dg_(A, d) ⥤ Comp^dg(B)` be a functor of
differential graded categories over `R` from the differential graded modules over `A` to the
cochain complexes in `B`. Then `F` induces an
ordinary functor `Mod_(A, d) ⥤ Comp(B)` which descends to the homotopy categories, and the
descended functor is exact: it commutes with the translation and carries distinguished triangles
to distinguished triangles.

The mechanism is that `F` acts on *all* homogeneous morphisms, not only on the closed ones of
degree zero. An admissible short exact sequence of differential graded `A`-modules is split by
homogeneous morphisms of degree zero, so `F` transports the splittings and the image sequence is
a degreewise split short exact sequence of complexes in `B`, whose triangle is distinguished. The
same mechanism identifies `F` of the shift `M[n]` with the shift of `F M`, because the identity
of the underlying module is a homogeneous morphism `M[n] ⟶ M` of degree `n`.

## Main definitions

* `DifferentialGradedModule.dgFunctorToComplexes`: the induced functor `Mod_(A, d) ⥤ Comp(B)`.
* `DifferentialGradedModule.dgFunctorToHomotopyCategory`: the induced functor `K(A, d) ⥤ K(B)`.

## Main results

* `DifferentialGradedModule.dgFunctorToComplexes_obj` and
  `DifferentialGradedModule.dgFunctorToComplexes_map_f`: the induced functor is `F` on objects
  and is given componentwise by `F` on morphisms.
* `DifferentialGradedModule.dgFunctorToHomotopyCategory_spec`: the induced functor on homotopy
  categories is the lift of the induced functor on complexes along the two quotient functors.
* `DifferentialGradedModule.dgFunctorToHomotopyCategoryCommShift` and
  `DifferentialGradedModule.dgFunctorToHomotopyCategory_isTriangulated`: the induced functor on
  homotopy categories is exact.

## Implementation notes

*The shift comparison is the image of a homogeneous morphism.* The identity of the underlying
module is a homogeneous morphism `M[n] ⟶ M` of degree `n`, closed because the differential of
`M[n]` is `(-1)^n` times that of `M`; its image under `F` is a closed homogeneous morphism of
degree `n`, that is, a map of complexes `F(M[n]) ⟶ F(M)[n]`. The homogeneous morphism in the
other direction has degree `-n`, and the two composites are identities already as homogeneous
morphisms, so the comparison is an isomorphism of complexes and no computation with cones is
needed. The two coherence axioms of a `CommShift` structure are checked the same way, since the
comparison homomorphisms `M[0] ⟶ M` and `M[a + b] ⟶ (M[a])[b]` are also the identity on
underlying modules.

*The triangles come from the splittings, not from cones.* The pretriangulated structure used on
`K(A, d)` is `DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished
triangles are, by `DifferentialGradedModule.distinguishedTriangles_eq`, those isomorphic to the
triangle of an admissible short exact sequence. Admissibility provides compatible graded
splittings `s` and `π`, and the images of those under `F` split the image short complex in each
degree; Mathlib's `CochainComplex.trianglehOfDegreewiseSplit_distinguished` then applies. The
connecting morphisms match because the connecting homomorphism of the source sequence is
`π ∘ d ∘ s`, which `F` carries to the cochain computing Mathlib's connecting cochain, using that
`F` commutes with the differential of the Hom complexes.

*Why the graded identities are isolated in their own section.* The identities between
homogeneous morphisms used below — that the two shift comparisons are mutually inverse, that the
images of the splittings split, and the formula for the connecting homomorphism — are proved in
the first section, where only the source differential graded category occurs. At `R = ℤ`, which
is the base ring at which the consumers of this file read a merely preadditive `B`, the
`ℤ`-module structure carried by a differential graded module is not the one that instance
synthesis finds, so an element of a `ℤ`-linear Hom-module cannot be introduced or extended
there; stating these identities without reference to the target and only rewriting with them
afterwards avoids the issue entirely.

*The target is the `R`-linear differential graded category of complexes.*
`CochainComplex.dgCategoryLinear B R` has the objects, homogeneous morphisms, differential,
composition and identities of `CochainComplex.dgCategory B` — all five by `rfl` — and adds the
`R`-module structure on the homogeneous morphisms. Reading the target there rather than at
`CochainComplex.dgCategory B` is therefore no change at `R = ℤ`, and it is what lets a
differential graded functor out of the modules over a differential graded `R`-algebra be
descended at all: a differential graded functor has a single base ring, and the endomorphism
algebra of a complex of `O`-modules for `O` a sheaf of commutative `R`-algebras is a
differential graded `R`-algebra.

## References

* [Stacks Project, Tag 09L8](https://stacks.math.columbia.edu/tag/09L8)
* [Stacks Project, Tag 09K8](https://stacks.math.columbia.edu/tag/09K8)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

universe r u v w t

section GradedIdentities

variable {R : Type r} [CommRing R] {A : DifferentialGradedAlgebra.{r, u} R}

/-- A graded homomorphism, read as a homogeneous morphism of degree zero of the differential
graded category of differential graded modules. -/
public def homogeneousMapOfGradedHom {M N : DifferentialGradedModule.{r, u, t} A}
    (f : GradedHom M N) : (dgCategory.{r, u, t} A).Hom M N 0 :=
  ⟨f.toFun, fun i x hx => by simpa using f.map_grading i x hx, fun a x => f.map_smul x a⟩

/-- The identity of the underlying module, read as a homogeneous morphism `M[n] ⟶ M` of
degree `n`. -/
public noncomputable def homogeneousMapFromShift
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgCategory.{r, u, t} A).Hom (shift M n) M n :=
  ⟨LinearMap.id, fun _ _ hx => hx, fun _ _ => rfl⟩

/-- The identity of the underlying module, read as a homogeneous morphism `M ⟶ M[n]` of
degree `-n`. -/
public noncomputable def homogeneousMapToShift
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgCategory.{r, u, t} A).Hom M (shift M n) (-n) :=
  ⟨LinearMap.id, fun i x hx => by
    change x ∈ M.grading (i + -n + n)
    simpa using hx, fun _ _ => rfl⟩

public lemma homogeneousMapFromShift_closed (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgCategory.{r, u, t} A).d (homogeneousMapFromShift M n) = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change M.d x - DifferentialGraded.gradedSign R n • (n.negOnePow • M.d x) = 0
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow,
    smul_smul,
    show DifferentialGraded.gradedSign R n * DifferentialGraded.gradedSign R n = 1 by
      rw [← DifferentialGraded.intCast_negOnePow, ← Int.cast_mul, ← Units.val_mul,
        Int.units_mul_self, Units.val_one, Int.cast_one],
    one_smul, sub_self]

public lemma homogeneousMapToShift_comp_fromShift
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgCategory.{r, u, t} A).comp (neg_add_cancel n) (homogeneousMapToShift M n)
        (homogeneousMapFromShift M n) =
      (dgCategory.{r, u, t} A).id (shift M n) := rfl

public lemma homogeneousMapFromShift_comp_toShift
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgCategory.{r, u, t} A).comp (add_neg_cancel n) (homogeneousMapFromShift M n)
        (homogeneousMapToShift M n) =
      (dgCategory.{r, u, t} A).id M := rfl

public lemma homogeneousMapFromShift_zero (M : DifferentialGradedModule.{r, u, t} A) :
    homogeneousMapFromShift M 0 = (cocycleOfHom A (shiftZeroHom A M)).1 := rfl

public lemma homogeneousMapFromShift_add (M : DifferentialGradedModule.{r, u, t} A) (a b : ℤ) :
    (dgCategory.{r, u, t} A).comp (add_zero (a + b))
        ((dgCategory.{r, u, t} A).comp rfl (homogeneousMapFromShift M a)
          (homogeneousMapFromShift (shift M a) b))
        (cocycleOfHom A (shiftAddHom A M a b)).1 =
      homogeneousMapFromShift M (a + b) := rfl

private lemma comp_eq_zero_of_admissible {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : IsAdmissibleShortExact f g) : f ≫ g = 0 := by
  apply DifferentialGradedModule.Hom.ext
  apply LinearMap.ext
  intro x
  change g.toFun (f.toFun x) = 0
  have h : f.toFun x ∈ LinearMap.range f.toFun := ⟨x, rfl⟩
  rw [hfg.exact] at h
  exact h

private lemma retraction_comp_eq_id {L M : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (π : GradedHom M L) (hπ : ∀ x : L.M, π.toFun (f.toFun x) = x) :
    (dgCategory.{r, u, t} A).comp (add_zero 0) (homogeneousMapOfGradedHom π)
        (cocycleOfHom A f).1 = (dgCategory.{r, u, t} A).id L :=
  Subtype.ext (LinearMap.ext hπ)

private lemma comp_section_eq_id {M N : DifferentialGradedModule.{r, u, t} A}
    (g : M ⟶ N) (s : GradedHom N M) (hs : ∀ x : N.M, g.toFun (s.toFun x) = x) :
    (dgCategory.{r, u, t} A).comp (add_zero 0) (cocycleOfHom A g).1
        (homogeneousMapOfGradedHom s) = (dgCategory.{r, u, t} A).id N :=
  Subtype.ext (LinearMap.ext hs)

private lemma compatibleSplittings_π_s {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : Hom L M) (g : Hom M N) (c : CompatibleSplittings A f g) (z : N.M) :
    c.π.toFun (c.s.toFun z) = 0 := by
  have hz : c.s.toFun z ∈ LinearMap.range c.s.toFun := ⟨z, rfl⟩
  rw [← c.hker] at hz
  exact hz

private lemma compatibleSplittings_decomposition
    {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : Hom L M) (g : Hom M N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) (x : M.M) :
    f.toFun (c.π.toFun x) + c.s.toFun (g.toFun x) = x := by
  have hker : x - c.s.toFun (g.toFun x) ∈ LinearMap.ker g.toFun := by
    change g.toFun (x - c.s.toFun (g.toFun x)) = 0
    simp [c.hs]
  rw [← hfg.exact] at hker
  obtain ⟨y, hy⟩ := hker
  have hy' : y = c.π.toFun x := by
    simpa only [c.hπ, map_sub, compatibleSplittings_π_s f g c, sub_zero] using
      congrArg c.π.toFun hy
  rw [← hy', hy, sub_add_cancel]

private lemma splittings_sum_eq_id {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : Hom L M) (g : Hom M N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (dgCategory.{r, u, t} A).comp (add_zero 0) (cocycleOfHom A f).1
          (homogeneousMapOfGradedHom c.π) +
        (dgCategory.{r, u, t} A).comp (add_zero 0) (homogeneousMapOfGradedHom c.s)
          (cocycleOfHom A g).1 =
      (dgCategory.{r, u, t} A).id M :=
  Subtype.ext (LinearMap.ext (compatibleSplittings_decomposition f g hfg c))

/-- The connecting homomorphism of an admissible short exact sequence, read inside the
differential graded category: it is `π ∘ d ∘ s`. -/
private lemma connectingCochain_eq {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : Hom L M) (g : Hom M N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (dgCategory.{r, u, t} A).comp (zero_add 1) (homogeneousMapOfGradedHom c.π)
        ((dgCategory.{r, u, t} A).d (homogeneousMapOfGradedHom c.s)) =
      (dgCategory.{r, u, t} A).comp (add_zero 1) (homogeneousMapFromShift L 1)
        (cocycleOfHom A (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val).1 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change c.π.toFun (M.d (c.s.toFun x) -
      DifferentialGraded.gradedSign R 0 • c.s.toFun (N.d x)) =
    (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun x
  rw [(connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property,
    DifferentialGraded.gradedSign, Int.natAbs_zero, pow_zero, one_smul,
    map_sub, compatibleSplittings_π_s f g c, sub_zero]

end GradedIdentities

section DGFunctor

variable {R : Type r} [CommRing R] {A : DifferentialGradedAlgebra.{r, u} R}
  {B : Type v} [Category.{w} B] [Preadditive B] [Linear R B]
  (F : DGCategory.DGFunctor (dgCategory.{r, u, t} A) (CochainComplex.dgCategoryLinear B R))

/-! ### The induced functor on differential graded modules -/

/-- A functor of differential graded categories from the differential graded modules over `A` to
the cochain complexes in `B` induces an ordinary functor from the differential graded `A`-modules
to the cochain complexes in `B`: on objects it is `F`, and the image of a homomorphism is the
chain map whose components are the components of the image of the associated closed degree-zero
homogeneous morphism. -/
@[implicit_reducible]
public def dgFunctorToComplexes :
    DifferentialGradedModule.{r, u, t} A ⥤ CochainComplex B ℤ where
  obj M := F.obj M
  map f := Cocycle.homOf
    (Cocycle.mk (F.map (cocycleOfHom A f).1) 1 rfl (F.map_cocycle (cocycleOfHom A f)))
  map_id M := by
    ext i
    change (F.map ((dgCategory.{r, u, t} A).id M)).v i i _ = _
    rw [F.map_id, CochainComplex.dgCategoryLinear_id_v]
    rfl
  map_comp f g := by
    ext i
    change (F.map ((dgCategory.{r, u, t} A).comp (by omega) (cocycleOfHom A g).1
      (cocycleOfHom A f).1)).v i i _ = _
    rw [F.map_comp, CochainComplex.dgCategoryLinear_comp_v (B := B) (R := R) _ _ _ i i i
      (add_zero i) (add_zero i)]
    rfl

@[simp] public theorem dgFunctorToComplexes_obj (M : DifferentialGradedModule.{r, u, t} A) :
    (dgFunctorToComplexes F).obj M = F.obj M := rfl

@[simp] public theorem dgFunctorToComplexes_map_f
    {M N : DifferentialGradedModule.{r, u, t} A} (f : M ⟶ N) (i : ℤ) :
    ((dgFunctorToComplexes F).map f).f i = (F.map (cocycleOfHom A f).1).v i i (add_zero i) := rfl

/-- The image under `F` of a composite of homogeneous morphisms, on components. -/
public lemma dgFunctor_map_comp_v {L M N : DifferentialGradedModule.{r, u, t} A}
    {m n k : ℤ} (h : m + n = k) (g : (dgCategory.{r, u, t} A).Hom M N m)
    (f : (dgCategory.{r, u, t} A).Hom L M n) (i j l : ℤ) (hij : i + n = j) (hjl : j + m = l) :
    (F.map ((dgCategory.{r, u, t} A).comp h g f)).v i l (by omega) =
      (F.map f).v i j hij ≫ (F.map g).v j l hjl := by
  rw [F.map_comp, CochainComplex.dgCategoryLinear_comp_v (B := B) (R := R) h _ _ i j l hij hjl]

/-- If two homogeneous morphisms compose to the identity, their images compose to the identity
on components. -/
private lemma dgFunctor_map_v_comp_eq_id {L M : DifferentialGradedModule.{r, u, t} A} {m n : ℤ}
    (g : (dgCategory.{r, u, t} A).Hom M L m) (f : (dgCategory.{r, u, t} A).Hom L M n)
    (h : m + n = 0) (hgf : (dgCategory.{r, u, t} A).comp h g f = (dgCategory.{r, u, t} A).id L)
    (i j : ℤ) (hij : i + n = j) (hji : j + m = i) :
    (F.map f).v i j hij ≫ (F.map g).v j i hji = 𝟙 _ := by
  rw [← dgFunctor_map_comp_v F h g f i j i hij hji, hgf, F.map_id,
    CochainComplex.dgCategoryLinear_id_v]

/-! ### Commutation with the shift -/

/-- The comparison `F(M[n]) ⟶ F(M)[n]`, the image of the degree-`n` homogeneous morphism
`M[n] ⟶ M`. -/
public noncomputable def dgFunctorToComplexesShiftHom
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgFunctorToComplexes F).obj (shift M n) ⟶ ((dgFunctorToComplexes F).obj M)⟦n⟧ :=
  Cocycle.homOf ((Cocycle.mk (F.map (homogeneousMapFromShift M n)) (n + 1) rfl (by
    change (CochainComplex.dgCategoryLinear B R).d (F.map (homogeneousMapFromShift M n)) = 0
    rw [← F.map_d, homogeneousMapFromShift_closed, F.map_zero])).rightShift n 0 (zero_add n))

public lemma dgFunctorToComplexesShiftHom_f
    (M : DifferentialGradedModule.{r, u, t} A) (n i : ℤ) :
    (dgFunctorToComplexesShiftHom F M n).f i =
      (F.map (homogeneousMapFromShift M n)).v i (i + n) rfl := by
  simp [dgFunctorToComplexesShiftHom, Cocycle.homOf_f, Cochain.rightShift_v,
    CochainComplex.shiftFunctorObjXIso]

/-- The comparison `F(M[n]) ≅ F(M)[n]`. Its inverse is the image of the degree-`-n` homogeneous
morphism `M ⟶ M[n]`. -/
public noncomputable def dgFunctorToComplexesShiftIso
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    (dgFunctorToComplexes F).obj (shift M n) ≅ ((dgFunctorToComplexes F).obj M)⟦n⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun i => {
    hom := (F.map (homogeneousMapFromShift M n)).v i (i + n) rfl
    inv := (F.map (homogeneousMapToShift M n)).v (i + n) i (by omega)
    hom_inv_id := by
      have h := congrArg (fun z => z.v i i (add_zero i))
        (F.map_comp (neg_add_cancel n) (homogeneousMapToShift M n) (homogeneousMapFromShift M n))
      rw [homogeneousMapToShift_comp_fromShift, F.map_id] at h
      simpa only [dgFunctorToComplexes, CochainComplex.shiftFunctor_obj_X',
        CochainComplex.dgCategoryLinear_comp_v (B := B) (R := R) _
          (F.map (homogeneousMapToShift M n))
          (F.map (homogeneousMapFromShift M n)) i (i + n) i rfl (by omega),
        CochainComplex.dgCategoryLinear_id_v] using h.symm
    inv_hom_id := by
      have h := congrArg (fun z => z.v (i + n) (i + n) (add_zero (i + n)))
        (F.map_comp (add_neg_cancel n) (homogeneousMapFromShift M n) (homogeneousMapToShift M n))
      rw [homogeneousMapFromShift_comp_toShift, F.map_id] at h
      simpa only [dgFunctorToComplexes, CochainComplex.shiftFunctor_obj_X',
        CochainComplex.dgCategoryLinear_comp_v (B := B) (R := R) _
          (F.map (homogeneousMapFromShift M n))
          (F.map (homogeneousMapToShift M n)) (i + n) i (i + n) (by omega) rfl,
        CochainComplex.dgCategoryLinear_id_v] using h.symm }) (by
      intro i j hij
      simpa only [← dgFunctorToComplexesShiftHom_f] using
        (dgFunctorToComplexesShiftHom F M n).comm i j)

public lemma dgFunctorToComplexesShiftIso_hom_f
    (M : DifferentialGradedModule.{r, u, t} A) (n i : ℤ) :
    (dgFunctorToComplexesShiftIso F M n).hom.f i =
      (F.map (homogeneousMapFromShift M n)).v i (i + n) rfl := rfl

public noncomputable def dgFunctorToComplexesShiftNatIso (n : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule.{r, u, t} A) n ⋙
        dgFunctorToComplexes F ≅
      dgFunctorToComplexes F ⋙ CategoryTheory.shiftFunctor (CochainComplex B ℤ) n :=
  NatIso.ofComponents (fun M => dgFunctorToComplexesShiftIso F M n) (by
    intro M N f
    ext i
    change ((dgFunctorToComplexes F).map (shiftMap f n)).f i ≫
        (dgFunctorToComplexesShiftIso F N n).hom.f i =
      (dgFunctorToComplexesShiftIso F M n).hom.f i ≫ ((dgFunctorToComplexes F).map f).f (i + n)
    rw [dgFunctorToComplexes_map_f, dgFunctorToComplexesShiftIso_hom_f,
      dgFunctorToComplexesShiftIso_hom_f, dgFunctorToComplexes_map_f]
    rw [← dgFunctor_map_comp_v F (add_zero n) (homogeneousMapFromShift N n)
        (cocycleOfHom A (shiftMap f n)).1 i i (i + n) (add_zero i) rfl,
      ← dgFunctor_map_comp_v F (zero_add n) (cocycleOfHom A f).1 (homogeneousMapFromShift M n)
        i (i + n) (i + n) rfl (add_zero (i + n))]
    rfl)

/-- The induced functor on complexes commutes with the translation. -/
public noncomputable instance dgFunctorToComplexesCommShift :
    (dgFunctorToComplexes F).CommShift ℤ where
  commShiftIso := dgFunctorToComplexesShiftNatIso F
  commShiftIso_zero := by
    ext M i
    simp only [Functor.CommShift.isoZero_hom_app, dgFunctorToComplexesShiftNatIso,
      NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, dgFunctorToComplexesShiftIso_hom_f,
      dgFunctorToComplexes_map_f]
    rw [CochainComplex.shiftFunctorZero_inv_app_f]
    change _ = (F.map (cocycleOfHom A (shiftZeroHom A M)).1).v i i _ ≫
      ((F.obj M).XIsoOfEq (show i = i + 0 by omega)).hom
    rw [Cochain.v_comp_XIsoOfEq_hom, ← homogeneousMapFromShift_zero]
  commShiftIso_add a b := by
    ext M i
    simp only [Functor.CommShift.isoAdd_hom_app, dgFunctorToComplexesShiftNatIso,
      NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, dgFunctorToComplexesShiftIso_hom_f,
      dgFunctorToComplexes_map_f]
    rw [CochainComplex.shiftFunctor_map_f', dgFunctorToComplexesShiftIso_hom_f,
      CochainComplex.shiftFunctorAdd_inv_app_f]
    change _ = _ ≫ _ ≫ (F.map (homogeneousMapFromShift M a)).v (i + b) (i + b + a) _ ≫
      ((F.obj M).XIsoOfEq (show i + b + a = i + (a + b) by omega)).hom
    rw [Cochain.v_comp_XIsoOfEq_hom]
    change _ = (F.map (cocycleOfHom A (shiftAddHom A M a b)).1).v i i _ ≫
      (F.map (homogeneousMapFromShift (shift M a) b)).v i (i + b) _ ≫
        (F.map (homogeneousMapFromShift M a)).v (i + b) (i + (a + b)) _
    rw [← dgFunctor_map_comp_v F rfl (homogeneousMapFromShift M a)
        (homogeneousMapFromShift (shift M a) b) i (i + b) (i + (a + b)) rfl (by omega),
      ← dgFunctor_map_comp_v F (add_zero (a + b))
        ((dgCategory.{r, u, t} A).comp rfl (homogeneousMapFromShift M a)
          (homogeneousMapFromShift (shift M a) b))
        (cocycleOfHom A (shiftAddHom A M a b)).1 i i (i + (a + b)) (add_zero i) rfl,
      homogeneousMapFromShift_add]

/-! ### The image of an admissible short exact sequence -/

/-- The image under `F` of an admissible short exact sequence, as a short complex of cochain
complexes. -/
private def dgFunctorToComplexesShortComplex {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : IsAdmissibleShortExact f g) :
    CategoryTheory.ShortComplex (CochainComplex B ℤ) :=
  CategoryTheory.ShortComplex.mk ((dgFunctorToComplexes F).map f)
    ((dgFunctorToComplexes F).map g) (by
      rw [← Functor.map_comp, comp_eq_zero_of_admissible f g hfg]
      ext i
      change (F.map (0 : (dgCategory.{r, u, t} A).Hom L N 0)).v i i (add_zero i) = 0
      rw [F.map_zero, Cochain.zero_v])

/-- The image short complex is split in each degree, by the images of the compatible graded
splittings of the source sequence. -/
private def dgFunctorToComplexesSplitting {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) (i : ℤ) :
    ((dgFunctorToComplexesShortComplex F f g hfg).map
      (HomologicalComplex.eval B (ComplexShape.up ℤ) i)).Splitting where
  r := (F.map (homogeneousMapOfGradedHom c.π)).v i i (add_zero i)
  s := (F.map (homogeneousMapOfGradedHom c.s)).v i i (add_zero i)
  f_r := by
    change (F.map (cocycleOfHom A f).1).v i i _ ≫
      (F.map (homogeneousMapOfGradedHom c.π)).v i i _ = 𝟙 _
    exact dgFunctor_map_v_comp_eq_id F _ _ (add_zero 0) (retraction_comp_eq_id f c.π c.hπ) i i
      (add_zero i) (add_zero i)
  s_g := by
    change (F.map (homogeneousMapOfGradedHom c.s)).v i i _ ≫
      (F.map (cocycleOfHom A g).1).v i i _ = 𝟙 _
    exact dgFunctor_map_v_comp_eq_id F _ _ (add_zero 0) (comp_section_eq_id g c.s c.hs) i i
      (add_zero i) (add_zero i)
  id := by
    change (F.map (homogeneousMapOfGradedHom c.π)).v i i _ ≫ (F.map (cocycleOfHom A f).1).v i i _ +
      (F.map (cocycleOfHom A g).1).v i i _ ≫
        (F.map (homogeneousMapOfGradedHom c.s)).v i i _ = 𝟙 _
    rw [← dgFunctor_map_comp_v F (add_zero 0) (cocycleOfHom A f).1 (homogeneousMapOfGradedHom c.π)
        i i i (add_zero i) (add_zero i),
      ← dgFunctor_map_comp_v F (add_zero 0) (homogeneousMapOfGradedHom c.s) (cocycleOfHom A g).1
        i i i (add_zero i) (add_zero i), ← Cochain.add_v, ← F.map_add,
      splittings_sum_eq_id f g hfg c, F.map_id, CochainComplex.dgCategoryLinear_id_v]

/-- The image of the connecting homomorphism is, through the shift comparison, Mathlib's
connecting morphism of the image degreewise split sequence. -/
private lemma map_connectingHom {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (dgFunctorToComplexes F).map
        (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫
          (dgFunctorToComplexesShiftIso F L 1).hom =
      CochainComplex.homOfDegreewiseSplit (dgFunctorToComplexesShortComplex F f g hfg)
        (dgFunctorToComplexesSplitting F f g hfg c) := by
  ext i
  rw [HomologicalComplex.comp_f, dgFunctorToComplexes_map_f, dgFunctorToComplexesShiftIso_hom_f,
    ← dgFunctor_map_comp_v F (add_zero 1) (homogeneousMapFromShift L 1)
      (cocycleOfHom A (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val).1
      i i (i + 1) (add_zero i) rfl,
    ← connectingCochain_eq f g hfg c,
    dgFunctor_map_comp_v F (zero_add 1) (homogeneousMapOfGradedHom c.π)
      ((dgCategory.{r, u, t} A).d (homogeneousMapOfGradedHom c.s)) i (i + 1) (i + 1) rfl
      (add_zero (i + 1)),
    F.map_d, CochainComplex.homOfDegreewiseSplit_f]
  change (δ 0 1 (F.map (homogeneousMapOfGradedHom c.s))).v i (i + 1) rfl ≫
      (F.map (homogeneousMapOfGradedHom c.π)).v (i + 1) (i + 1) _ =
    (F.map (homogeneousMapOfGradedHom c.s)).v i i _ ≫ (F.obj M).d i (i + 1) ≫
      (F.map (homogeneousMapOfGradedHom c.π)).v (i + 1) (i + 1) _
  have hs := (dgFunctorToComplexesSplitting F f g hfg c (i + 1)).s_r
  change (F.map (homogeneousMapOfGradedHom c.s)).v (i + 1) (i + 1) _ ≫
    (F.map (homogeneousMapOfGradedHom c.π)).v (i + 1) (i + 1) _ = 0 at hs
  rw [δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Category.assoc, hs,
    CategoryTheory.Limits.comp_zero, sub_zero]

/-! ### The induced functor on homotopy categories -/

/-- A functor of differential graded categories preserves homotopy of cocycles. -/
public lemma dgFunctor_mapCocycle_homotopic {S : Type*} [CommRing S] {C D : DGCategory S}
    (G : DGCategory.DGFunctor C D) {L M : C.Obj} (p q : C.Cocycle L M)
    (h : C.Homotopic p q) : D.Homotopic (G.mapCocycle p) (G.mapCocycle q) :=
  Quotient.exact (congrArg G.mapHomotopyClass (Quotient.sound h))

/-- Two chain maps whose components are those of homotopic cocycles are homotopic. -/
public lemma homotopy_of_dgCategory_homotopic {L M : CochainComplex B ℤ}
    (p q : (CochainComplex.dgCategory B).Cocycle L M) (p' q' : L ⟶ M)
    (hp : ∀ i, p'.f i = p.1.v i i (add_zero i))
    (hq : ∀ i, q'.f i = q.1.v i i (add_zero i))
    (h : (CochainComplex.dgCategory B).Homotopic p q) :
    Nonempty (_root_.Homotopy p' q') := by
  have hp' : Cochain.ofHom p' = p.1 := by
    ext i; simpa only [Cochain.ofHom_v] using hp i
  have hq' : Cochain.ofHom q' = q.1 := by
    ext i; simpa only [Cochain.ofHom_v] using hq i
  obtain ⟨a, ha⟩ := h
  refine ⟨(Cochain.equivHomotopy p' q').symm ⟨a, ?_⟩⟩
  rw [hp', hq']
  exact sub_eq_iff_eq_add.mp ha

public lemma dgFunctorToComplexes_homotopy {M N : DifferentialGradedModule.{r, u, t} A}
    (f g : M ⟶ N) (h : Homotopic f g) :
    Nonempty (_root_.Homotopy ((dgFunctorToComplexes F).map f)
      ((dgFunctorToComplexes F).map g)) :=
  homotopy_of_dgCategory_homotopic (F.mapCocycle (cocycleOfHom A f))
    (F.mapCocycle (cocycleOfHom A g)) _ _ (fun _ => rfl) (fun _ => rfl)
    (dgFunctor_mapCocycle_homotopic F _ _ (cocycleOfHom_homotopic A h))

/-- The functor induced on homotopy categories by a functor of differential graded categories
from the differential graded modules over `A` to the cochain complexes in `B`. -/
@[implicit_reducible]
public def dgFunctorToHomotopyCategory :
    HomotopyCategory.{r, u, t} A ⥤ _root_.HomotopyCategory B (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopyRel A)
    (dgFunctorToComplexes F ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ))
    (fun _ _ f g h => by
      obtain ⟨H⟩ := dgFunctorToComplexes_homotopy F f g h
      exact HomotopyCategory.eq_of_homotopy _ _ H)

/-- The induced functor on homotopy categories lifts the induced functor on complexes. -/
public theorem dgFunctorToHomotopyCategory_spec :
    toHomotopyCategory A ⋙ dgFunctorToHomotopyCategory F =
      dgFunctorToComplexes F ⋙ HomotopyCategory.quotient B (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

public theorem dgFunctorToHomotopyCategory_map
    {M N : DifferentialGradedModule.{r, u, t} A} (f : M ⟶ N) :
    (dgFunctorToHomotopyCategory F).map ((toHomotopyCategory A).map f) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((dgFunctorToComplexes F).map f) := rfl

/-- The induced functor on homotopy categories commutes with the translation. -/
public noncomputable instance dgFunctorToHomotopyCategoryCommShift :
    (dgFunctorToHomotopyCategory F).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift _ _ _ _

private lemma quotient_commShiftIso_hom {C : Type*} [Category C] [HasShift C ℤ]
    (q : HomRel C) [q.IsCompatibleWithShift ℤ] (M : C) (n : ℤ) :
    ((CategoryTheory.Quotient.functor q).commShiftIso n).hom.app M =
      eqToHom (CategoryTheory.Quotient.functor_obj_shift q ℤ M n).symm := by
  unfold Functor.commShiftIso CategoryTheory.Quotient.functor_commShift
    Functor.CommShift.ofInduced
  simp only [Iso.symm_hom, CategoryTheory.Quotient.lift.isLift_inv]
  unfold HasShift.quotient
  rfl

public lemma homotopyCategory_commShiftIso_hom
    (M : DifferentialGradedModule.{r, u, t} A) (n : ℤ) :
    ((dgFunctorToHomotopyCategory F).commShiftIso n).hom.app ((toHomotopyCategory A).obj M) =
      (dgFunctorToHomotopyCategory F).map
          (((toHomotopyCategory A).commShiftIso n).inv.app M) ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
            (dgFunctorToComplexesShiftIso F M n).hom ≫
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso n).hom.app
            ((dgFunctorToComplexes F).obj M) := by
  change (CategoryTheory.Quotient.LiftCommShift.iso _ _ _ n).hom.app _ = _
  rw [CategoryTheory.Quotient.LiftCommShift.iso_hom_app,
    Functor.commShiftIso_comp_hom_app]
  rfl

private noncomputable def dgFunctorToComplexesTriangleIso
    {L M N : DifferentialGradedModule.{r, u, t} A}
    (f : L ⟶ M) (g : M ⟶ N) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings A f g) :
    (dgFunctorToHomotopyCategory F).mapTriangle.obj
        (associatedTriangleOfSplittings A f g hfg c) ≅
      CochainComplex.trianglehOfDegreewiseSplit (dgFunctorToComplexesShortComplex F f g hfg)
        (dgFunctorToComplexesSplitting F f g hfg c) := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · change (dgFunctorToHomotopyCategory F).map ((toHomotopyCategory A).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((dgFunctorToComplexes F).map f)
    rw [Category.comp_id, Category.id_comp, dgFunctorToHomotopyCategory_map]
  · change (dgFunctorToHomotopyCategory F).map ((toHomotopyCategory A).map g) ≫ 𝟙 _ =
      𝟙 _ ≫ (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((dgFunctorToComplexes F).map g)
    rw [Category.comp_id, Category.id_comp, dgFunctorToHomotopyCategory_map]
  · change
      ((dgFunctorToHomotopyCategory F).map
        ((toHomotopyCategory A).map
          (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫
          eqToHom (CategoryTheory.Quotient.functor_obj_shift
            (homotopyRel A) ℤ L 1).symm) ≫
        ((dgFunctorToHomotopyCategory F).commShiftIso 1).hom.app
          ((toHomotopyCategory A).obj L)) ≫
        (CategoryTheory.shiftFunctor (_root_.HomotopyCategory B (ComplexShape.up ℤ)) 1).map
          (𝟙 ((dgFunctorToHomotopyCategory F).obj ((toHomotopyCategory A).obj L))) =
      𝟙 ((dgFunctorToHomotopyCategory F).obj ((toHomotopyCategory A).obj N)) ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (CochainComplex.homOfDegreewiseSplit (dgFunctorToComplexesShortComplex F f g hfg)
            (dgFunctorToComplexesSplitting F f g hfg c)) ≫
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso 1).hom.app
          ((dgFunctorToComplexes F).obj L)
    simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp, Functor.map_comp, homotopyCategory_commShiftIso_hom,
      ← quotient_commShiftIso_hom (homotopyRel A), Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, dgFunctorToHomotopyCategory_map]
    have hid := (dgFunctorToHomotopyCategory F).map_id
      ((toHomotopyCategory A).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule.{r, u, t} A) (1 : ℤ)).obj L))
    rw [hid]
    refine (congrArg (fun z => (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((dgFunctorToComplexes F).map
          (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val) ≫ z)
      (Category.id_comp _)).trans ?_
    rw [← Functor.map_comp_assoc, map_connectingHom]
    rfl

/-- **The exactness of the induced functor.** The functor induced on homotopy categories carries
distinguished triangles to distinguished triangles: a distinguished triangle of `K(A, d)` is
isomorphic to the triangle of an admissible short exact sequence, whose image is a degreewise
split short exact sequence of complexes in `B`. -/
public theorem dgFunctorToHomotopyCategory_isTriangulated [Limits.HasZeroObject B]
    [Limits.HasBinaryBiproducts B] : (dgFunctorToHomotopyCategory F).IsTriangulated where
  map_distinguished T hT := by
    rw [distinguishedTriangles_eq] at hT
    obtain ⟨L, M, N, f, g, hfg, c, ⟨e⟩⟩ := (isDistinguishedTriangle_iff A T).mp hT
    refine Pretriangulated.isomorphic_distinguished _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished
        (dgFunctorToComplexesShortComplex F f g hfg)
        (dgFunctorToComplexesSplitting F f g hfg c)) _ ?_
    exact ((dgFunctorToHomotopyCategory F).mapTriangle.mapIso e) ≪≫
      dgFunctorToComplexesTriangleIso F f g hfg c

end DGFunctor

end DifferentialGradedModule

end
