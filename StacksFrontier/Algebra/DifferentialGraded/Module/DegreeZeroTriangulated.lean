module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure

/-!
# Exactness of the degree-zero comparison

Let `R` be a commutative ring, `S` an `R`-algebra and `A` an `R`-algebra identified with the
opposite algebra of `S`. Taking homogeneous components identifies the differential graded
`S`-modules placed in degree zero with the cochain complexes of `A`-modules, and this file proves
that the identification is *exact*: it carries the distinguished triangles of
`K(degreeZero R S, d)` — the triangles of admissible short exact sequences, by
`DifferentialGradedModule.distinguishedTriangles_eq` — to distinguished triangles of `K(A)`.

The mechanism is the one of Tag 09L8: an admissible short exact sequence carries compatible
graded splittings, their homogeneous components split the image short complex of complexes in
every degree, and Mathlib's `CochainComplex.trianglehOfDegreewiseSplit_distinguished` declares
the triangle of a degreewise split short exact sequence of complexes distinguished. The
connecting morphisms match because the connecting homomorphism of the source sequence is
`π ∘ d_L ∘ s`, which is literally the cochain Mathlib builds from the degreewise splittings.

## Main definitions

* `DifferentialGradedModule.degreeZeroHomotopyFunctor`: the functor
  `K(degreeZero R S, d) ⥤ K(A)` induced by taking homogeneous components.
* `DifferentialGradedModule.degreeZeroShortComplex` and
  `DifferentialGradedModule.degreeZeroSplitting`: the image of an admissible short exact sequence
  as a short complex of cochain complexes, together with the degreewise splitting its compatible
  graded splittings provide.

## Main results

* `DifferentialGradedModule.degreeZeroComponent_connectingHom`: the image of the connecting
  homomorphism is the morphism Mathlib builds from the degreewise splittings.
* `DifferentialGradedModule.degreeZeroHomotopyFunctor_isTriangulated`: the functor on homotopy
  categories is exact.

## Implementation notes

The homotopy-level functor is the lift of `degreeZeroComponentFunctor R A` along the two homotopy
quotients, which is possible because `DifferentialGradedModule.degreeZeroHomotopy` carries a
homotopy of homomorphisms of differential graded modules to a homotopy of the induced chain maps;
its commutation with the shift is then the one `CategoryTheory.Quotient.liftCommShift` induces
from `DifferentialGradedModule.degreeZeroComponentFunctor_commShift`.

The comparison of triangles is assembled on the *differential graded* triangle
`K ⟶ L ⟶ M ⟶ K[1]` whose third arrow is the connecting homomorphism: the triangle of Tag 09K8 is
its image under the homotopy quotient — the two spellings of the comparison with the shift being
identified by `DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom` — and
the triangle of the degreewise split sequence is its image under the homogeneous-components
functor, so the two are compared by the two factorizations of the homotopy-level functor through
the homotopy quotient.

## References

* [Stacks Project, Tag 09SC](https://stacks.math.columbia.edu/tag/09SC)
* [Stacks Project, Tag 09L8](https://stacks.math.columbia.edu/tag/09L8)
* [Stacks Project, Tag 09K8](https://stacks.math.columbia.edu/tag/09K8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedAlgebra

universe u w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {S : Type u} [Ring S] [Algebra R S] [IsOppositeAlgebra R S A]

attribute [local instance] degreeZeroOppositeModule degreeZeroComponentModule
attribute [local instance 10000] instPretriangulatedHomotopyCategory'

/-! ### The functor on homotopy categories -/

/-- Homotopic homomorphisms of differential graded modules have homotopic images: this is what
lets the homogeneous-components functor be lifted to the homotopy categories. -/
theorem degreeZeroComponent_quotient_map_eq
    (M N : DifferentialGradedModule (degreeZero R S)) (f g : M ⟶ N) (h : Homotopic f g) :
    (degreeZeroComponentFunctor R A ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map f =
      (degreeZeroComponentFunctor R A ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map g :=
  _root_.HomotopyCategory.eq_of_homotopy _ _ (degreeZeroHomotopy (A := A) h.some)

/-- **The homogeneous-components functor on homotopy categories.** The functor
`K(degreeZero R S, d) ⥤ K(A)` carrying the homotopy class of a homomorphism to the homotopy class
of the induced chain map of complexes of homogeneous components. -/
def degreeZeroHomotopyFunctor (R : Type u) [CommRing R] {S : Type u} [Ring S] [Algebra R S]
    (A : Type u) [Ring A] [Algebra R A] [IsOppositeAlgebra R S A] :
    HomotopyCategory (degreeZero R S) ⥤
      _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopyRel (degreeZero R S))
    (degreeZeroComponentFunctor R A ⋙
      _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ))
    degreeZeroComponent_quotient_map_eq

/-- The homotopy-level functor lifts the homogeneous-components functor. -/
theorem degreeZeroHomotopyFunctor_spec :
    toHomotopyCategory (degreeZero R S) ⋙ degreeZeroHomotopyFunctor R A =
      degreeZeroComponentFunctor R A ⋙
        _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- **The homotopy-level functor commutes with the translation.** -/
instance degreeZeroHomotopyFunctor_commShift :
    (degreeZeroHomotopyFunctor R A (S := S)).CommShift ℤ := by
  dsimp only [degreeZeroHomotopyFunctor]
  infer_instance

/-! ### The image of an admissible short exact sequence -/

/-- A graded homomorphism of differential graded modules over `degreeZero R S`, read in each
degree as a map of `A`-modules between the homogeneous components. -/
def degreeZeroGradedHomMap {M N : DifferentialGradedModule (degreeZero R S)}
    (f : GradedHom M N) (n : ℤ) :
    ModuleCat.of A (M.grading n) ⟶ ModuleCat.of A (N.grading n) :=
  ModuleCat.ofHom
    { toFun x := ⟨f.toFun x, f.map_grading n x x.property⟩
      map_add' x y := Subtype.ext (f.toFun.map_add x y)
      map_smul' a x := Subtype.ext (f.map_smul x ((oppositeEquiv R S A a).unop)) }

/-- The image of an admissible short exact sequence of differential graded modules under the
homogeneous-components functor, as a short complex of cochain complexes of `A`-modules. -/
def degreeZeroShortComplex {K L M : DifferentialGradedModule (degreeZero R S)}
    (f : K ⟶ L) (g : L ⟶ M) (hfg : IsAdmissibleShortExact f g) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk ((degreeZeroComponentFunctor R A).map f)
    ((degreeZeroComponentFunctor R A).map g) (by
      ext n x
      apply Subtype.ext
      change g.toFun (f.toFun x.val) = 0
      apply LinearMap.mem_ker.mp
      rw [← hfg.exact]
      exact ⟨x.val, rfl⟩)

/-- The compatible graded splittings of an admissible short exact sequence split the image short
complex of cochain complexes in every degree. -/
def degreeZeroSplitting {K L M : DifferentialGradedModule (degreeZero R S)}
    (f : K ⟶ L) (g : L ⟶ M) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings (degreeZero R S) f g) (n : ℤ) :
    ((degreeZeroShortComplex (A := A) f g hfg).map
      (HomologicalComplex.eval _ _ n)).Splitting where
  r := degreeZeroGradedHomMap (A := A) c.π n
  s := degreeZeroGradedHomMap (A := A) c.s n
  f_r := by ext x; exact Subtype.ext (c.hπ x.val)
  s_g := by ext x; exact Subtype.ext (c.hs x.val)
  id := by
    ext x
    apply Subtype.ext
    change f.toFun (c.π.toFun x.val) + c.s.toFun (g.toFun x.val) = x.val
    have hpis (y : M.M) : c.π.toFun (c.s.toFun y) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [c.hker]
      exact ⟨y, rfl⟩
    have hgf (y : K.M) : g.toFun (f.toFun y) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hfg.exact]
      exact ⟨y, rfl⟩
    have hq0 : x.val - f.toFun (c.π.toFun x.val) - c.s.toFun (g.toFun x.val) = 0 := by
      have hqp : c.π.toFun (x.val - f.toFun (c.π.toFun x.val) -
          c.s.toFun (g.toFun x.val)) = 0 := by
        simp [c.hπ, hpis]
      have hqg : g.toFun (x.val - f.toFun (c.π.toFun x.val) -
          c.s.toFun (g.toFun x.val)) = 0 := by
        simp [hgf, c.hs]
      obtain ⟨y, hy⟩ : x.val - f.toFun (c.π.toFun x.val) - c.s.toFun (g.toFun x.val) ∈
          LinearMap.range c.s.toFun := by
        rw [← c.hker]; exact hqp
      have hy0 : y = 0 := by rw [← c.hs y, hy, hqg]
      simpa [hy0] using hy.symm
    have hy := sub_eq_zero.mp hq0
    rw [sub_eq_iff_eq_add] at hy
    simpa [add_comm] using hy.symm

/-- **The connecting homomorphism is the cochain of the degreewise splitting.** The image of the
connecting homomorphism `δ = π ∘ d_L ∘ s` under the homogeneous-components functor, followed by
the comparison with the shift, is the morphism `M ⟶ K[1]` that Mathlib builds from the degreewise
splittings. -/
theorem degreeZeroComponent_connectingHom
    {K L M : DifferentialGradedModule (degreeZero R S)}
    (f : K ⟶ L) (g : L ⟶ M) (hfg : IsAdmissibleShortExact f g)
    (c : CompatibleSplittings (degreeZero R S) f g) :
    (degreeZeroComponentFunctor R A).map
        (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫
      ((degreeZeroComponentFunctor R A).commShiftIso (1 : ℤ)).hom.app K =
    CochainComplex.homOfDegreewiseSplit (degreeZeroShortComplex (A := A) f g hfg)
      (degreeZeroSplitting (A := A) f g hfg c) := by
  ext n x
  change ↥(M.grading n) at x
  apply Subtype.ext
  simp only [CochainComplex.homOfDegreewiseSplit_f, CochainComplex.cocycleOfDegreewiseSplit]
  change (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val.toFun x.val =
    (((degreeZeroSplitting (A := A) f g hfg c n).s ≫
      (degreeZeroShortComplex (A := A) f g hfg).X₂.d n (n + 1) ≫
      (degreeZeroSplitting (A := A) f g hfg c (n + 1)).r).hom x).val
  rw [(connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).property,
    show (degreeZeroShortComplex (A := A) f g hfg).X₂.d n (n + 1) =
      degreeZeroComplexDiff (A := A) L n from degreeZeroComplex_d_self (A := A) L n]
  rfl

/-! ### Exactness -/

/-- **The degree-zero comparison is exact on homotopy categories.** The functor
`K(degreeZero R S, d) ⥤ K(A)` carries distinguished triangles to distinguished triangles: a
distinguished triangle of `K(degreeZero R S, d)` is isomorphic to the triangle of an admissible
short exact sequence, whose image is a degreewise split short exact sequence of cochain
complexes. -/
@[stacks 09SC "exactness of the degree-zero comparison on homotopy categories"]
theorem degreeZeroHomotopyFunctor_isTriangulated :
    (degreeZeroHomotopyFunctor R A (S := S)).IsTriangulated := by
  refine ⟨fun T hT => ?_⟩
  rw [distinguishedTriangles_eq] at hT
  obtain ⟨K, L, M, f, g, hfg, c, ⟨e⟩⟩ := (isDistinguishedTriangle_iff (degreeZero R S) T).mp hT
  refine Pretriangulated.isomorphic_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished
      (degreeZeroShortComplex (A := A) f g hfg) (degreeZeroSplitting (A := A) f g hfg c)) _ ?_
  refine (degreeZeroHomotopyFunctor R A).mapTriangle.mapIso e ≪≫ ?_
  set Q := toHomotopyCategory (degreeZero R S)
  set G := degreeZeroComponentFunctor R A (S := S)
  set Q' := _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  set Td : Pretriangulated.Triangle (DifferentialGradedModule (degreeZero R S)) :=
    Pretriangulated.Triangle.mk f g
      (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val
  have hQ : associatedTriangleOfSplittings (degreeZero R S) f g hfg c = Q.mapTriangle.obj Td := by
    change Pretriangulated.Triangle.mk _ _ _ = Pretriangulated.Triangle.mk _ _ _
    congr 1
    exact congrArg
      (fun q => Q.map (connectingHom f g hfg c.s c.π c.hs c.hπ c.hker).val ≫ q)
      (toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom (degreeZero R S) K 1).symm
  have hG : G.mapTriangle.obj Td = CochainComplex.triangleOfDegreewiseSplit
      (degreeZeroShortComplex (A := A) f g hfg) (degreeZeroSplitting (A := A) f g hfg c) := by
    change Pretriangulated.Triangle.mk _ _ _ = Pretriangulated.Triangle.mk _ _ _
    exact congrArg (fun δ => Pretriangulated.Triangle.mk (G.map f) (G.map g) δ)
      (degreeZeroComponent_connectingHom (A := A) f g hfg c)
  rw [hQ]
  exact (Functor.mapTriangleCompIso Q (degreeZeroHomotopyFunctor R A)).symm.app Td ≪≫
    (Functor.mapTriangleIso
      (CategoryTheory.Quotient.lift.isLift (homotopyRel (degreeZero R S))
        (degreeZeroComponentFunctor R A ⋙
          _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ))
        degreeZeroComponent_quotient_map_eq)).app Td ≪≫
    (Functor.mapTriangleCompIso G Q').app Td ≪≫ Q'.mapTriangle.mapIso (eqToIso hG)

/-! ### Exactness of the comparison equivalence of derived categories -/

section Derived

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The comparison equivalence of derived categories, read through the homotopy category of
differential graded modules: the two factorizations of the homogeneous-components functor through
the derived category of `A`-modules — along the homotopy category of cochain complexes, and along
the localization of differential graded modules — agree. -/
def degreeZeroDerivedHomotopyComponentIso :
    toHomotopyCategory (degreeZero R S) ⋙
        ((quasiIsomorphisms' (degreeZero R S)).Q ⋙
          (degreeZeroDerivedEquivalence (R := R) (A := A)).functor) ≅
      toHomotopyCategory (degreeZero R S) ⋙
        (degreeZeroHomotopyFunctor R A ⋙ DerivedCategory.Qh) :=
  (Functor.associator _ _ _).symm ≪≫ degreeZeroDerivedComponentIso ≪≫
    Functor.isoWhiskerLeft (degreeZeroComponentFunctor R A)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso degreeZeroHomotopyFunctor_spec).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **The comparison equivalence of derived categories lifts the homotopy-level comparison.** -/
def degreeZeroDerivedHomotopyIso :
    (quasiIsomorphisms' (degreeZero R S)).Q ⋙
        (degreeZeroDerivedEquivalence (R := R) (A := A)).functor ≅
      degreeZeroHomotopyFunctor R A ⋙ DerivedCategory.Qh :=
  CategoryTheory.Quotient.natIsoLift _ degreeZeroDerivedHomotopyComponentIso

/-- The comparison equivalence lifts the homotopy-level comparison followed by the localization
of cochain complexes, along the localization of the homotopy category of differential graded
modules at the quasi-isomorphisms. -/
instance degreeZeroDerivedHomotopyLifting :
    Localization.Lifting (quasiIsomorphisms' (degreeZero R S)).Q
      (quasiIsomorphisms' (degreeZero R S))
      (degreeZeroHomotopyFunctor R A ⋙ DerivedCategory.Qh)
      (degreeZeroDerivedEquivalence (R := R) (A := A)).functor :=
  ⟨degreeZeroDerivedHomotopyIso⟩

/-- **The comparison equivalence of derived categories is exact.** For the commutation with the
shift that the localization of the homotopy category induces on it, the equivalence
`D(degreeZero R S, d) ≌ D(A)` carries distinguished triangles to distinguished triangles: it
lifts the exact functor `K(degreeZero R S, d) ⥤ D(A)` of
`DifferentialGradedModule.degreeZeroHomotopyFunctor_isTriangulated` along a localization of
pretriangulated categories, and such a lift is exact. -/
@[stacks 09SC "exactness of the degree-zero comparison equivalence of derived categories"]
theorem degreeZeroDerivedEquivalence_functor_exact :
    ∃ h : (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.CommShift ℤ, letI := h;
      (degreeZeroDerivedEquivalence (R := R) (A := A)).functor.IsTriangulated := by
  have := degreeZeroHomotopyFunctor_isTriangulated (R := R) (S := S) (A := A)
  have := Localization.essSurj_mapArrow (quasiIsomorphisms' (degreeZero R S)).Q
    (quasiIsomorphisms' (degreeZero R S))
  let h := Functor.commShiftOfLocalization (quasiIsomorphisms' (degreeZero R S)).Q
    (quasiIsomorphisms' (degreeZero R S)) ℤ
    (degreeZeroHomotopyFunctor R A ⋙ DerivedCategory.Qh)
    (degreeZeroDerivedEquivalence (R := R) (A := A)).functor
  refine ⟨h, ?_⟩
  let := h
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso (quasiIsomorphisms' (degreeZero R S)).Q
      (quasiIsomorphisms' (degreeZero R S))
      (degreeZeroHomotopyFunctor R A ⋙ DerivedCategory.Qh)
      (degreeZeroDerivedEquivalence (R := R) (A := A)).functor)

end Derived

end DifferentialGradedModule

end
