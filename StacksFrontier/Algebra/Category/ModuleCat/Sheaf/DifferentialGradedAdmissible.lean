module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule

/-!
# Admissible short exact sequences of differential graded modules over a sheaf of algebras

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded `R`-algebras.
A pair of morphisms `f : K ⟶ L`, `g : L ⟶ M` of right differential graded `A`-modules is an
*admissible short exact sequence* when it is split after forgetting the differentials: there are
homomorphisms `r : L ⟶ K` and `s : M ⟶ L` of the underlying graded `A`-modules with `f ≫ r = 1`,
`s ≫ g = 1` and `r ≫ f + g ≫ s = 1`. The splitting maps are *not* required to commute with the
differentials, which is the whole point of the notion.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GradedSplitting` is a splitting of a pair of
  morphisms at the graded level, and
  `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact` says that one exists.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.shortComplex` and
  `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.shortComplex` are the
  resulting short complex of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.splitting` is the splitting of the
  underlying short complex of graded modules, in the sense of
  `CategoryTheory.ShortComplex.Splitting`.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.ofBiprod` splits the inclusion and
  the projection of a biproduct.

## Main results

* `SheafOfModules.DifferentialGradedModule.GradedSplitting.comp_eq_zero`: the composite of an
  admissible short exact sequence vanishes. It is not a hypothesis: the three splitting
  identities force it.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.shortExact` and
  `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.shortExact`: an admissible
  short exact sequence is short exact.

## Implementation notes

The splitting is data and `IsAdmissibleShortExact` is its `Nonempty`, as on the ring side
`StacksFrontier/Algebra/DifferentialGraded/Module/LeftNativeCover.lean`, where admissibility of a
monomorphism and of an epimorphism are existence statements. Carrying the data separately is what
lets a consumer transport a chosen splitting.

Vanishing of the composite is derived rather than assumed. Writing `p` and `q` for the two
morphisms of graded modules, composing the decomposition of the identity with `p` on the left
gives `p ≫ q ≫ s = 0`, and composing that with `q` on the right gives `p ≫ q = 0` because `s` is
a section of `q`; faithfulness of forgetting the differential then returns the identity for the
differential graded morphisms.

Short exactness is a consequence, not part of the definition: a split short complex of graded
modules is exact, forgetting the differential detects exactness
(`SheafOfModules.DifferentialGradedModule.exact_iff_forgetToGradedModule_exact`) and a faithful
functor reflects monomorphisms and epimorphisms. This is where `HasSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat` enter: they are what make graded and differential
graded modules abelian, and hence what makes "exact" meaningful. The definition itself needs
neither.

The base is an arbitrary sheaf of rings on an arbitrary site, and the universes of the site, the
ring, the homogeneous pieces of the algebra and those of the modules are independent, as in the
neighbouring differential graded files.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, a} R}
  {K L M : DifferentialGradedModule.{t, a, m} A}

/-- A *graded splitting* of a pair of morphisms `f : K ⟶ L`, `g : L ⟶ M` of right differential
graded modules: a retraction of `f` and a section of `g`, homomorphisms of the underlying graded
modules, which decompose the identity of `L`. -/
structure GradedSplitting (f : K ⟶ L) (g : L ⟶ M) where
  /-- A retraction of `f`, a homomorphism of the underlying graded modules. -/
  r : GradedModule.ofDifferentialGraded L ⟶ GradedModule.ofDifferentialGraded K
  /-- A section of `g`, a homomorphism of the underlying graded modules. -/
  s : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded L
  /-- The retraction splits `f`. -/
  f_r : GradedModule.ofDifferentialGradedMap f ≫ r = 𝟙 _
  /-- The section splits `g`. -/
  s_g : s ≫ GradedModule.ofDifferentialGradedMap g = 𝟙 _
  /-- The retraction and the section decompose the identity of the middle module. -/
  id : r ≫ GradedModule.ofDifferentialGradedMap f +
    GradedModule.ofDifferentialGradedMap g ≫ s = 𝟙 _

namespace GradedSplitting

variable {f : K ⟶ L} {g : L ⟶ M}

/-- The composite of the two underlying homomorphisms of graded modules vanishes. -/
theorem graded_comp_eq_zero (S : GradedSplitting f g) :
    GradedModule.ofDifferentialGradedMap f ≫ GradedModule.ofDifferentialGradedMap g = 0 := by
  have h₁ : GradedModule.ofDifferentialGradedMap f ≫
      GradedModule.ofDifferentialGradedMap g ≫ S.s = 0 := by
    have e : GradedModule.ofDifferentialGradedMap f ≫
          (S.r ≫ GradedModule.ofDifferentialGradedMap f +
            GradedModule.ofDifferentialGradedMap g ≫ S.s) =
        GradedModule.ofDifferentialGradedMap f ≫ 𝟙 _ := by
      rw [S.id]
    rw [Preadditive.comp_add, ← Category.assoc, S.f_r, Category.id_comp,
      Category.comp_id] at e
    exact add_left_cancel (e.trans (add_zero _).symm)
  calc GradedModule.ofDifferentialGradedMap f ≫ GradedModule.ofDifferentialGradedMap g
      = GradedModule.ofDifferentialGradedMap f ≫ GradedModule.ofDifferentialGradedMap g ≫
          (S.s ≫ GradedModule.ofDifferentialGradedMap g) := by
        rw [S.s_g, Category.comp_id]
    _ = (GradedModule.ofDifferentialGradedMap f ≫
          GradedModule.ofDifferentialGradedMap g ≫ S.s) ≫
            GradedModule.ofDifferentialGradedMap g := by
        simp only [Category.assoc]
    _ = 0 := by rw [h₁, zero_comp]

/-- **The composite of an admissible short exact sequence vanishes**: the three splitting
identities force it. -/
theorem comp_eq_zero (S : GradedSplitting f g) : f ≫ g = 0 :=
  have := forgetToGradedModule_faithful.{t, a, m} A
  (forgetToGradedModule A).map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    exact S.graded_comp_eq_zero)

/-- The short complex of right differential graded modules of an admissible short exact
sequence. -/
def shortComplex (S : GradedSplitting f g) :
    ShortComplex (DifferentialGradedModule.{t, a, m} A) :=
  ShortComplex.mk f g S.comp_eq_zero

/-- The first map of `shortComplex` is `f`. -/
@[simp] theorem shortComplex_f (S : GradedSplitting f g) : S.shortComplex.f = f := rfl

/-- The second map of `shortComplex` is `g`. -/
@[simp] theorem shortComplex_g (S : GradedSplitting f g) : S.shortComplex.g = g := rfl

/-- The underlying short complex of graded modules of an admissible short exact sequence is
split. -/
def splitting (S : GradedSplitting f g) :
    (S.shortComplex.map (forgetToGradedModule A)).Splitting where
  r := S.r
  s := S.s
  f_r := S.f_r
  s_g := S.s_g
  id := S.id

section Exactness

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **An admissible short exact sequence of right differential graded modules is short
exact.** -/
theorem shortExact (S : GradedSplitting f g) : S.shortComplex.ShortExact :=
  have := forgetToGradedModule_faithful.{t, a, m} A
  { exact := (exact_iff_forgetToGradedModule_exact A S.shortComplex).2
      S.splitting.shortExact.exact
    mono_f := (forgetToGradedModule A).mono_of_mono_map
      (f := S.shortComplex.f) S.splitting.shortExact.mono_f
    epi_g := (forgetToGradedModule A).epi_of_epi_map
      (f := S.shortComplex.g) S.splitting.shortExact.epi_g }

end Exactness

/-- The inclusion of the first summand and the projection to the second summand of a biproduct
of right differential graded modules are an admissible short exact sequence. -/
noncomputable def ofBiprod (K M : DifferentialGradedModule.{t, a, m} A)
    [HasBinaryBiproduct K M] :
    GradedSplitting (Limits.biprod.inl : K ⟶ K ⊞ M) (Limits.biprod.snd : K ⊞ M ⟶ M) where
  r := GradedModule.ofDifferentialGradedMap Limits.biprod.fst
  s := GradedModule.ofDifferentialGradedMap Limits.biprod.inr
  f_r := by
    rw [← GradedModule.ofDifferentialGradedMap_comp, Limits.biprod.inl_fst,
      GradedModule.ofDifferentialGradedMap_id]
  s_g := by
    rw [← GradedModule.ofDifferentialGradedMap_comp, Limits.biprod.inr_snd,
      GradedModule.ofDifferentialGradedMap_id]
  id := by
    rw [← GradedModule.ofDifferentialGradedMap_comp,
      ← GradedModule.ofDifferentialGradedMap_comp,
      show GradedModule.ofDifferentialGradedMap (Limits.biprod.fst ≫ Limits.biprod.inl) +
          GradedModule.ofDifferentialGradedMap (Limits.biprod.snd ≫ Limits.biprod.inr) =
            GradedModule.ofDifferentialGradedMap
              (Limits.biprod.fst ≫ Limits.biprod.inl +
                Limits.biprod.snd ≫ Limits.biprod.inr) from
        (GradedModule.Hom.ext fun _ ↦ rfl),
      Limits.biprod.total, GradedModule.ofDifferentialGradedMap_id]

end GradedSplitting

/-- A pair of morphisms `f : K ⟶ L`, `g : L ⟶ M` of right differential graded modules is an
*admissible short exact sequence* when it is split after forgetting the differentials. -/
def IsAdmissibleShortExact (f : K ⟶ L) (g : L ⟶ M) : Prop :=
  Nonempty (GradedSplitting f g)

namespace IsAdmissibleShortExact

variable {f : K ⟶ L} {g : L ⟶ M}

/-- The composite of an admissible short exact sequence vanishes. -/
theorem comp_eq_zero (h : IsAdmissibleShortExact f g) : f ≫ g = 0 :=
  Nonempty.elim h fun S ↦ S.comp_eq_zero

/-- The short complex of right differential graded modules of an admissible short exact
sequence. -/
def shortComplex (h : IsAdmissibleShortExact f g) :
    ShortComplex (DifferentialGradedModule.{t, a, m} A) :=
  ShortComplex.mk f g h.comp_eq_zero

/-- **An admissible short exact sequence of right differential graded modules is short
exact.** -/
theorem shortExact [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] (h : IsAdmissibleShortExact f g) :
    h.shortComplex.ShortExact :=
  Nonempty.elim h fun S ↦ S.shortExact

end IsAdmissibleShortExact

/-- The inclusion of the first summand and the projection to the second summand of a biproduct
of right differential graded modules are an admissible short exact sequence. -/
theorem isAdmissibleShortExact_biprod (K M : DifferentialGradedModule.{t, a, m} A)
    [HasBinaryBiproduct K M] :
    IsAdmissibleShortExact (Limits.biprod.inl : K ⟶ K ⊞ M) (Limits.biprod.snd : K ⊞ M ⟶ M) :=
  ⟨GradedSplitting.ofBiprod K M⟩

end DifferentialGradedModule

end SheafOfModules
