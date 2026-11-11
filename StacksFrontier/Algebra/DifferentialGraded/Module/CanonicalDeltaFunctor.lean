module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.ConeMap
public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.LongExactSequence
public import StacksFrontier.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCore.Algebra.Homology.HomologicalComplexAbelian

/-!
# The canonical delta-functor to the derived category of a differential graded algebra

Let `(A, d)` be a differential graded algebra. The canonical functor
`Mod_{(A, d)} ⥤ D(A, d)` — the quotient by homotopy followed by the localization at the
quasi-isomorphisms — carries the structure of a `δ`-functor: to a short exact sequence
`0 → K → L → M → 0` of differential graded modules one attaches a connecting morphism built from
`q : C(f) → M`, the comparison of the mapping cone of `f : K ⟶ L` with the quotient `M` (a
quasi-isomorphism, hence invertible in `D(A, d)`), and `p : C(f) → K[1]`, the cone projection; the
image of the sequence is then a distinguished triangle and the connecting morphism is natural.

Which sign the connecting morphism carries depends on the triangulation. In the Stacks project's
convention, where `(K, L, C(f), f, i, -p)` is distinguished (Tag 09KF), it is `δ = - p ∘ q⁻¹`;
in the library's default convention, where the unsigned cone triangle `(K, L, C(f), f, i, p)` is
distinguished, it is `p ∘ q⁻¹`. This file proves the latter; the former is
`StacksFrontier.Algebra.DifferentialGraded.Module.CanonicalDeltaFunctorStacksSign`.

## Main definitions

* `DifferentialGradedModule.toDerivedCategory`: the canonical functor `Mod_{(A,d)} ⥤ D(A, d)`.
* `DifferentialGradedModule.coneDescShortComplex`: the comparison `q : C(f) ⟶ M` of the mapping
  cone of the first map of a short complex with its third term, `(l, k) ↦ g l`.
* `DifferentialGradedModule.coneIdToConeShortComplex`: the inclusion `C(1_K) ⟶ C(f)` of the
  cone of the identity of the first term, which is the kernel of that comparison.

## Main results

* `DifferentialGradedModule.quasiIso_coneDescShortComplex`: for a short exact sequence the
  comparison `C(f) ⟶ M` is a quasi-isomorphism.
* `DifferentialGradedModule.exists_deltaFunctorStructure_δ_eq_neg`: **Stacks 09L0** — against
  the triangulation of Tag 09KH (`DifferentialGradedModule.derivedCategory'`), in which
  `(K, L, C(f), f, i, -p)` is distinguished, the canonical functor carries a `δ`-functor structure
  whose connecting morphism is `- p ∘ q⁻¹`.
* `DifferentialGradedModule.canonicalDeltaFunctorStructure` and
  `DifferentialGradedModule.canonicalDeltaFunctorStructure_δ_eq`: the same in the library's default
  sign convention (`DifferentialGradedModule.derivedCategory`, cone triangles distinguished), where
  the connecting morphism is `p ∘ q⁻¹`.

## Implementation notes

*Why the comparison `q` is a quasi-isomorphism.* The source leaves this to the general theory of
cones. Here it is proved from the short exact sequence of differential graded modules
`0 → C(1_K) → C(f) → M → 0`: the first map is `(k', k) ↦ (f k', k)`, which is injective because
`f` is, and the quotient by it is `M` because the kernel of `(l, k) ↦ g l` is exactly the image of
`f` in the first coordinate. The cone of an identity is contractible
(`DifferentialGradedModule.coneIdContraction`), hence has acyclic underlying cochain complex, and
a short exact sequence of cochain complexes whose first term is acyclic has its second map a
quasi-isomorphism (`CategoryTheory.ShortComplex.ShortExact.quasiIso_g_of_acyclic_X₁`). This route
needs no comparison of the differential graded cone with the mapping cone of complexes.

*A `δ`-functor structure is data, and the source pins it.* The statement is therefore the
existence of a `CategoryTheory.Functor.DeltaFunctorStructure` *together with* the equation
identifying its connecting morphism; since the two remaining fields of such a structure are
`Prop`-valued, that equation determines the structure.

*Signs.* The third morphism of `DifferentialGradedModule.coneTriangle` is the *unsigned* cone
projection `p` (composed with `DifferentialGradedModule.quotientShiftIso`), and the default
triangulation `DifferentialGradedModule.instPretriangulatedHomotopyCategory` declares those
triangles distinguished; against it, `canonicalDeltaFunctorStructure` has connecting morphism
`inv (Q q)` followed by `Q p` and the commutation of the localization with the shift, i.e.
`p ∘ q⁻¹`, *not* the source's `- p ∘ q⁻¹`. The Stacks project instead declares
`(K, L, C(f), f, i, -p)` distinguished (Tag 09KF); that is the triangulation
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'` of Tag 09KH, whose distinguished
triangles are those of admissible short exact sequences, and its localization
`DifferentialGradedModule.derivedCategory'`. Against it the connecting morphism is built from the
third morphism of `DifferentialGradedModule.mappingConeTriangle`, the class of `-p`, and is the
source's `- p ∘ q⁻¹` literally: `DifferentialGradedModule.exists_deltaFunctorStructure_δ_eq_neg`,
which carries Tag 09L0. The two triangulations differ exactly by negating third arrows
(`DifferentialGradedModule.mem_distinguishedConeTriangles_iff_isDistinguishedTriangle_negMor₃`),
so the two statements are the same result read through that sign dictionary.

*Naturality.* A morphism `φ` of short complexes induces `C(φ.τ₁, φ.τ₂) : C(f₁) ⟶ C(f₂)`
(`DifferentialGradedModule.coneMapOfHomotopy` applied to the commuting square, whose homotopy is
the zero one), and that morphism is compatible both with the comparisons `q` and with the cone
projections — the latter being the third commutation of
`DifferentialGradedModule.coneTriangleMapOfHomotopy`. Those two compatibilities are the naturality
square of `δ` after `q` has been inverted.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and the
modules live in a single universe `u`, following the bundled encoding of Tag 09JJ.

## References

* [Stacks Project, Tag 09L0](https://stacks.math.columbia.edu/tag/09L0); the mapping cone and its
  triangle are [Tag 09KA](https://stacks.math.columbia.edu/tag/09KA) and
  [Tag 09KF](https://stacks.math.columbia.edu/tag/09KF), the long exact cohomology sequence of a
  short exact sequence is [Tag 09JK](https://stacks.math.columbia.edu/tag/09JK), the derived
  category is [Tag 09KX](https://stacks.math.columbia.edu/tag/09KX) and the notion of a
  `δ`-functor is [Tag 0150](https://stacks.math.columbia.edu/tag/0150).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

/-! ### A short exact sequence of complexes with acyclic first term -/

/-- If the first term of a short exact sequence of homological complexes is acyclic, its second
map is a quasi-isomorphism: the long exact homology sequence has a zero term on either side of
`H(g)`, so `H(g)` is both a monomorphism and an epimorphism. -/
theorem CategoryTheory.ShortComplex.ShortExact.quasiIso_g_of_acyclic_X₁ {C : Type*} [Category C]
    [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
    (h₁ : S.X₁.Acyclic) : _root_.QuasiIso S.g := by
  have hz : ∀ i, IsZero (S.X₁.homology i) := fun i =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (h₁ i)
  rw [_root_.quasiIso_iff]
  intro i
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((hz i).eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.g i) := by
    by_cases hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      exact (hS.homology_exact₃ i j hij).epi_f ((hz j).eq_of_tgt _ _)
    · have := hS.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g i (by simpa using hi)
  exact isIso_of_mono_of_epi _

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The canonical functor from differential graded `A`-modules to the derived category
`D(A, d)`: the quotient by homotopy followed by the localization at the quasi-isomorphisms. -/
abbrev toDerivedCategory (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModule A ⥤ derivedCategory A :=
  toHomotopyCategory A ⋙ (quasiIsomorphisms A).Q

section Comparison

variable (S : ShortComplex (DifferentialGradedModule A))

/-- The comparison `C(f) ⟶ M` of the mapping cone of the first map of a short complex
`K --f--> L --g--> M` with its third term: on the underlying module `L × K` it is `(l, k) ↦ g l`,
which is a homomorphism because `f ≫ g = 0`. -/
def coneDescShortComplex : coneObject S.f ⟶ S.X₃ :=
  coneDesc S.f S.g (Homotopy.ofEq S.zero)

/-- On the underlying module `L × K` of the cone, the comparison `C(f) ⟶ M` sends `(l, k)` to
`g l`. -/
@[simp] theorem coneDescShortComplex_toFun_apply (x : (coneObject S.f).M) :
    (coneDescShortComplex S).toFun x = S.g.toFun x.1 := by
  change S.g.toFun x.1 + (Homotopy.ofEq S.zero).toLinearMap x.2 = _
  rw [show (Homotopy.ofEq S.zero).toLinearMap = 0 from rfl, LinearMap.zero_apply, add_zero]

/-- The comparison restricts along the inclusion of `L` into the cone to the second map of the
short complex. -/
@[simp] theorem coneIncl_coneDescShortComplex :
    coneIncl S.f ≫ coneDescShortComplex S = S.g :=
  coneIncl_coneDesc _ _ _

/-- The map of cones induced by a square commuting on the nose is `(l, k) ↦ (b l, a k)`. -/
private theorem coneMapOfHomotopy_ofEq_toFun_apply {K₁ L₁ K₂ L₂ : DifferentialGradedModule A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (h : f₁ ≫ b = a ≫ f₂)
    (x : (coneObject f₁).M) :
    (coneMapOfHomotopy (Homotopy.ofEq h)).toFun x = (b.toFun x.1, a.toFun x.2) := by
  change (b.toFun x.1 + (Homotopy.ofEq h).toLinearMap x.2, a.toFun x.2) = _
  rw [show (Homotopy.ofEq h).toLinearMap = 0 from rfl, LinearMap.zero_apply, add_zero]

/-- The inclusion `C(1_K) ⟶ C(f)` of the cone of the identity of the first term of a short
complex into the cone of its first map: on underlying modules `(k', k) ↦ (f k', k)`. -/
def coneIdToConeShortComplex : coneObject (𝟙 S.X₁) ⟶ coneObject S.f :=
  coneMapOfHomotopy (f₁ := 𝟙 S.X₁) (f₂ := S.f) (a := 𝟙 S.X₁) (b := S.f) (Homotopy.ofEq rfl)

/-- On underlying modules, the inclusion `C(1_K) ⟶ C(f)` sends `(k', k)` to `(f k', k)`. -/
@[simp] theorem coneIdToConeShortComplex_toFun_apply (x : (coneObject (𝟙 S.X₁)).M) :
    (coneIdToConeShortComplex S).toFun x = (S.f.toFun x.1, x.2) := by
  rw [coneIdToConeShortComplex, coneMapOfHomotopy_ofEq_toFun_apply]
  rfl

/-- The composite `C(1_K) ⟶ C(f) ⟶ M` of the inclusion and the comparison is zero. -/
theorem coneIdToConeShortComplex_comp_coneDescShortComplex :
    coneIdToConeShortComplex S ≫ coneDescShortComplex S = 0 := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  change (coneDescShortComplex S).toFun ((coneIdToConeShortComplex S).toFun x) = 0
  rw [coneIdToConeShortComplex_toFun_apply, coneDescShortComplex_toFun_apply]
  exact LinearMap.congr_fun (congrArg Hom.toFun S.zero) x.1

/-- The short complex `C(1_K) ⟶ C(f) ⟶ M` attached to a short complex
`K --f--> L --g--> M` of differential graded modules. -/
def coneDescSequence : ShortComplex (DifferentialGradedModule A) :=
  ShortComplex.mk (coneIdToConeShortComplex S) (coneDescShortComplex S)
    (coneIdToConeShortComplex_comp_coneDescShortComplex S)

/-- The cone of an identity has acyclic underlying cochain complex: its identity is homotopic to
zero, so the identity of each homology module is zero. -/
theorem acyclic_coneObject_id (K : DifferentialGradedModule A) :
    ((forgetToCochainComplex A).obj (coneObject (𝟙 K))).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa using homologyMap_eq_of_homotopic (A := A)
    (f := 𝟙 (coneObject (𝟙 K))) (g := 0) ⟨coneIdContraction K⟩ i

/-- In each degree, the sequence `C(1_K) ⟶ C(f) ⟶ M` is exact as soon as `K ⟶ L ⟶ M` is: the
kernel of `(l, k) ↦ g l` consists of the pairs whose first coordinate lies in the image of `f`. -/
private theorem exact_gradedMap_coneDescSequence (n : ℤ)
    (hex : Function.Exact (S.f.gradedMap n) (S.g.gradedMap n)) :
    Function.Exact ((coneIdToConeShortComplex S).gradedMap n)
      ((coneDescShortComplex S).gradedMap n) := by
  intro x
  constructor
  · intro hx
    have hx' : S.g.toFun (x.1 : (coneObject S.f).M).1 = 0 := by
      have h := congrArg Subtype.val hx
      change (coneDescShortComplex S).toFun x.1 = 0 at h
      rwa [coneDescShortComplex_toFun_apply] at h
    obtain ⟨a, ha⟩ := (hex ⟨(x.1 : (coneObject S.f).M).1,
      ((coneGrading_mem n _).mp x.2).1⟩).mp (Subtype.ext hx')
    refine ⟨⟨((a : S.X₁.M), (x.1 : (coneObject S.f).M).2),
      (coneGrading_mem n _).mpr ⟨a.2, ((coneGrading_mem n _).mp x.2).2⟩⟩, Subtype.ext ?_⟩
    change (coneIdToConeShortComplex S).toFun _ = _
    rw [coneIdToConeShortComplex_toFun_apply]
    exact Prod.ext (congrArg Subtype.val ha) rfl
  · rintro ⟨y, rfl⟩
    exact Subtype.ext (LinearMap.congr_fun
      (congrArg Hom.toFun (coneIdToConeShortComplex_comp_coneDescShortComplex S)) _)

/-- **The short complex `0 → C(1_K) → C(f) → M → 0` of a short exact sequence is short exact**,
degreewise on underlying cochain complexes. The first map is injective because `f` is; the kernel
of `(l, k) ↦ g l` is the set of pairs whose first coordinate lies in the image of `f`, which is
the image of the first map; and `(l, k) ↦ g l` is surjective because `g` is. -/
theorem shortExact_map_coneDescSequence (hS : S.ShortExact) :
    ((coneDescSequence S).map (forgetToCochainComplex A)).ShortExact := by
  have _ : Mono S.f := hS.mono_f
  have _ : Epi S.g := hS.epi_g
  have hSdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (shortExact_forgetToCochainComplex A S hS)
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact exact_gradedMap_coneDescSequence S n
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hSdeg n).exact)
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((coneIdToConeShortComplex S).gradedMap n)
    intro x y hxy
    have h := congrArg Subtype.val hxy
    change (coneIdToConeShortComplex S).toFun x.1 = (coneIdToConeShortComplex S).toFun y.1 at h
    rw [coneIdToConeShortComplex_toFun_apply, coneIdToConeShortComplex_toFun_apply,
      Prod.ext_iff] at h
    exact Subtype.ext (Prod.ext (Hom.injective_of_mono A S.f h.1) h.2)
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective ((coneDescShortComplex S).gradedMap n)
    intro y
    have hsurj : Function.Surjective (S.g.gradedMap n) :=
      (ModuleCat.epi_iff_surjective _).mp (hSdeg n).epi_g
    obtain ⟨l, hl⟩ := hsurj y
    refine ⟨⟨((l : S.X₂.M), (0 : S.X₁.M)),
      (coneGrading_mem n _).mpr ⟨l.2, (S.X₁.grading (n + 1)).zero_mem⟩⟩, Subtype.ext ?_⟩
    change (coneDescShortComplex S).toFun _ = _
    rw [coneDescShortComplex_toFun_apply]
    exact congrArg Subtype.val hl

/-- **The comparison `C(f) ⟶ M` of a short exact sequence is a quasi-isomorphism.** -/
theorem quasiIso_coneDescShortComplex (hS : S.ShortExact) :
    QuasiIso ((forgetToCochainComplex A).map (coneDescShortComplex S)) :=
  (shortExact_map_coneDescSequence S hS).quasiIso_g_of_acyclic_X₁ (acyclic_coneObject_id S.X₁)

/-- The comparison `C(f) ⟶ M` of a short exact sequence represents a quasi-isomorphism of the
homotopy category. -/
theorem quasiIsomorphisms_map_coneDescShortComplex (hS : S.ShortExact) :
    quasiIsomorphisms A ((toHomotopyCategory A).map (coneDescShortComplex S)) :=
  (quasiIsomorphisms_map_iff A _).2 (quasiIso_coneDescShortComplex S hS)

/-- The comparison `C(f) ⟶ M` of a short exact sequence becomes invertible in `D(A, d)`. -/
theorem isIso_toDerivedCategory_map_coneDescShortComplex (hS : S.ShortExact) :
    IsIso ((toDerivedCategory A).map (coneDescShortComplex S)) :=
  Localization.inverts (quasiIsomorphisms A).Q (quasiIsomorphisms A) _
    (quasiIsomorphisms_map_coneDescShortComplex S hS)

end Comparison

section DeltaFunctor

/-- The connecting morphism `p ∘ q⁻¹` of a short exact sequence of differential graded modules,
in the library's default sign convention: the inverse in `D(A, d)` of the comparison
`q : C(f) ⟶ M`, followed by the third morphism of the cone triangle of `f` (the class of the
unsigned cone projection `p`) read in `D(A, d)`. The Stacks project's `- p ∘ q⁻¹`, for its own
triangulation, is `DifferentialGradedModule.shortExactδ'`. -/
def shortExactδ {S : ShortComplex (DifferentialGradedModule A)} (hS : S.ShortExact) :
    (toDerivedCategory A).obj S.X₃ ⟶ ((toDerivedCategory A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  have := isIso_toDerivedCategory_map_coneDescShortComplex S hS
  inv ((toDerivedCategory A).map (coneDescShortComplex S)) ≫
    (quasiIsomorphisms A).Q.map
      ((toHomotopyCategory A).map (coneProj S.f) ≫ (quotientShiftIso S.X₁ 1).hom) ≫
      ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
        ((toHomotopyCategory A).obj S.X₁)

/-- The morphism of cones `C(f₁) ⟶ C(f₂)` induced by a morphism of short complexes. -/
def coneMapOfShortComplexHom {S₁ S₂ : ShortComplex (DifferentialGradedModule A)} (φ : S₁ ⟶ S₂) :
    coneObject S₁.f ⟶ coneObject S₂.f :=
  coneMapOfHomotopy (f₁ := S₁.f) (f₂ := S₂.f) (a := φ.τ₁) (b := φ.τ₂)
    (Homotopy.ofEq φ.comm₁₂.symm)

/-- The comparisons `C(f₁) ⟶ M₁` and `C(f₂) ⟶ M₂` commute with the morphism of cones and the
third component of a morphism of short complexes. -/
theorem coneMapOfShortComplexHom_comp_coneDescShortComplex
    {S₁ S₂ : ShortComplex (DifferentialGradedModule A)} (φ : S₁ ⟶ S₂) :
    coneMapOfShortComplexHom φ ≫ coneDescShortComplex S₂ =
      coneDescShortComplex S₁ ≫ φ.τ₃ := by
  apply Hom.ext
  refine LinearMap.ext fun x => ?_
  have h : ((coneMapOfShortComplexHom φ).toFun x).1 = φ.τ₂.toFun x.1 :=
    congrArg Prod.fst (coneMapOfHomotopy_ofEq_toFun_apply _ x)
  rw [Hom.comp_toFun_apply, Hom.comp_toFun_apply, coneDescShortComplex_toFun_apply,
    coneDescShortComplex_toFun_apply, h]
  have h2 := LinearMap.congr_fun (congrArg Hom.toFun φ.comm₂₃) x.1
  rwa [Hom.comp_toFun_apply, Hom.comp_toFun_apply] at h2

/-- The canonical functor `Mod_{(A, d)} → D(A, d)` has the structure of a `δ`-functor, for the
library's default triangulation of `D(A, d)` (cone triangles `(K, L, C(f), f, i, p)`
distinguished). The connecting morphism is `DifferentialGradedModule.shortExactδ`, identified
with `p ∘ q⁻¹` in `DifferentialGradedModule.canonicalDeltaFunctorStructure_δ_eq`. This is
Tag 09L0 read through the sign dictionary; the statement in the Stacks project's own convention,
with `δ = - p ∘ q⁻¹`, is `DifferentialGradedModule.exists_deltaFunctorStructure_δ_eq_neg`. -/
def canonicalDeltaFunctorStructure (A : DifferentialGradedAlgebra R) :
    (toDerivedCategory A).DeltaFunctorStructure (DifferentialGradedModule A)
      (derivedCategory A) where
  δ hS := shortExactδ hS
  distinguished {S} hS := by
    have hiso := isIso_toDerivedCategory_map_coneDescShortComplex S hS
    have hcomp := (toDerivedCategory A).map_comp (coneIncl S.f) (coneDescShortComplex S)
    rw [coneIncl_coneDescShortComplex] at hcomp
    refine isomorphic_distinguished _
      ((quasiIsomorphisms A).Q.map_distinguished _ (coneTriangle_mk_mem S.f)) _ ?_
    refine (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (asIso ((toDerivedCategory A).map (coneDescShortComplex S))).symm ?_ ?_ ?_)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change (toDerivedCategory A).map S.g ≫
          inv ((toDerivedCategory A).map (coneDescShortComplex S)) =
        𝟙 _ ≫ (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneIncl S.f))
      rw [Category.id_comp, IsIso.comp_inv_eq]
      exact hcomp
    · change shortExactδ hS ≫ (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map
            (𝟙 ((quasiIsomorphisms A).Q.obj ((toHomotopyCategory A).obj S.X₁))) =
          inv ((toDerivedCategory A).map (coneDescShortComplex S)) ≫
            (quasiIsomorphisms A).Q.map
              ((toHomotopyCategory A).map (coneProj S.f) ≫ (quotientShiftIso S.X₁ 1).hom) ≫
            ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
              ((toHomotopyCategory A).obj S.X₁)
      rw [show (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map
          (𝟙 ((quasiIsomorphisms A).Q.obj ((toHomotopyCategory A).obj S.X₁))) = 𝟙 _ from
        CategoryTheory.Functor.map_id _ _]
      exact Category.comp_id _
  δ_naturality {S₁ S₂} h₁ h₂ φ := by
    have hiso₁ := isIso_toDerivedCategory_map_coneDescShortComplex S₁ h₁
    have hiso₂ := isIso_toDerivedCategory_map_coneDescShortComplex S₂ h₂
    have hq := congrArg (toDerivedCategory A).map
      (coneMapOfShortComplexHom_comp_coneDescShortComplex φ)
    rw [Functor.map_comp, Functor.map_comp] at hq
    have hp : (quasiIsomorphisms A).Q.map
          (((toHomotopyCategory A).map (coneProj S₁.f) ≫ (quotientShiftIso S₁.X₁ 1).hom) ≫
            (CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
              ((toHomotopyCategory A).map φ.τ₁)) =
        (quasiIsomorphisms A).Q.map ((toHomotopyCategory A).map (coneMapOfShortComplexHom φ) ≫
          ((toHomotopyCategory A).map (coneProj S₂.f) ≫ (quotientShiftIso S₂.X₁ 1).hom)) :=
      congrArg _ (coneTriangleMapOfHomotopy (f₁ := S₁.f) (f₂ := S₂.f) (a := φ.τ₁) (b := φ.τ₂)
        (Homotopy.ofEq φ.comm₁₂.symm)).comm₃
    have hξ : ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory A).obj S₁.X₁) ≫
          (CategoryTheory.shiftFunctor (derivedCategory A) (1 : ℤ)).map
            ((toDerivedCategory A).map φ.τ₁) =
        (quasiIsomorphisms A).Q.map
            ((CategoryTheory.shiftFunctor (HomotopyCategory A) (1 : ℤ)).map
              ((toHomotopyCategory A).map φ.τ₁)) ≫
          ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
            ((toHomotopyCategory A).obj S₂.X₁) :=
      (((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.naturality
        ((toHomotopyCategory A).map φ.τ₁)).symm
    rw [shortExactδ, shortExactδ]
    apply (cancel_epi ((toDerivedCategory A).map (coneDescShortComplex S₁))).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc ((toDerivedCategory A).map (coneDescShortComplex S₁)), ← hq,
      Category.assoc, IsIso.hom_inv_id_assoc, hξ, ← Category.assoc,
      ← Functor.map_comp, hp, Functor.map_comp, Category.assoc]
    rfl

/-- The formula for the connecting morphism of the canonical `δ`-functor structure in the
library's default sign convention: it is `p ∘ q⁻¹`. Here `q` is the comparison `C(f) ⟶ M`, which
on the underlying module `L × K` is `(l, k) ↦ g l` and restricts along the inclusion of `L` to
`g`, and which is invertible in `D(A, d)`; and `p` is the third morphism of the cone triangle, the
*unsigned* cone projection `C(f) ⟶ K[1]`. The Stacks project's `δ = - p ∘ q⁻¹`, against its own
triangulation in which `(K, L, C(f), f, i, -p)` is distinguished, is
`DifferentialGradedModule.exists_deltaFunctorStructure_δ_eq_neg`. -/
theorem canonicalDeltaFunctorStructure_δ_eq
    {S : ShortComplex (DifferentialGradedModule A)} (hS : S.ShortExact) :
    (∀ x : (coneObject S.f).M, (coneDescShortComplex S).toFun x = S.g.toFun x.1) ∧
      coneIncl S.f ≫ coneDescShortComplex S = S.g ∧
      ∃ _ : IsIso ((toDerivedCategory A).map (coneDescShortComplex S)),
        (canonicalDeltaFunctorStructure A).δ hS =
          inv ((toDerivedCategory A).map (coneDescShortComplex S)) ≫
            (quasiIsomorphisms A).Q.map (coneTriangle S.f).mor₃ ≫
              ((quasiIsomorphisms A).Q.commShiftIso (1 : ℤ)).hom.app
                ((toHomotopyCategory A).obj S.X₁) :=
  ⟨coneDescShortComplex_toFun_apply S, coneIncl_coneDescShortComplex S,
    isIso_toDerivedCategory_map_coneDescShortComplex S hS, rfl⟩

end DeltaFunctor

end DifferentialGradedModule

end
