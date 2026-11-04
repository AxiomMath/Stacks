module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Leray spectral sequence of a continuous map, for sheaves of abelian groups

Let `f : X ⟶ Y` be a continuous map of topological spaces and let `K` be an object of
`D⁺(Sh(X, Ab))`. Taking global sections on `X` is taking global sections on `Y` of the direct
image, `Γ(X, -) = Γ(Y, -) ∘ f_*`, and the direct image of a sheaf of abelian groups carries
injective objects to injective objects. The Grothendieck spectral sequence of
[Stacks, Tag 015N] for this composition is a spectral sequence
```
E_2^{p,q} = H^p(Y, R^q f_* K)
```
which is bounded, converges to `H^*(X, K)` and induces a finite filtration on each
`H^n(X, K)`. As in [Stacks, Tag 015N], a spectral sequence converging to `H^*(K)` is presented
through a filtered complex whose spectral sequence it is, with pages the quotients
`Z_r^{p,q}/D_r^{p,q}` of [Stacks, Tag 012M].

The low-degree consequence of such a spectral sequence, the five term exact sequence
```
0 ⟶ E_2^{1,0} ⟶ H^1 ⟶ E_2^{0,1} ⟶ E_2^{2,0} ⟶ H^2,
```
is proved here for an arbitrary first quadrant `E₂` cohomological spectral sequence together
with a finite filtration of its abutment, in the section `FirstQuadrant`.

## Main definitions

* `sectionsFunctor`: the functor of sections over an open subset, `Γ(U, -)`.
* `pushforward`: the direct image `f_*` of sheaves of abelian groups.
* `inverseImage`: the inverse image `f^{-1}` of sheaves of abelian groups, the left adjoint
  of `pushforward`.
* `FirstQuadrantAbutment`: convergence data for a first quadrant `E₂` cohomological spectral
  sequence: a finite decreasing filtration of each term of a graded object, whose graded
  pieces are the terms of the infinity page.
* `FirstQuadrantAbutment.inflation`, `FirstQuadrantAbutment.restriction` and
  `FirstQuadrantAbutment.transgression`: the three edge maps of the five term exact sequence.

## Main results

* `pushforward_preservesInjectiveObjects`: `f_*` carries injective sheaves of abelian groups to
  injective sheaves of abelian groups.
* `rightAcyclic_of_injective`: an injective object is right acyclic for every additive functor.
* `rightAcyclic_pushforward_obj_of_injective`: the hypothesis of [Stacks, Tag 015N] for the
  pair `(f_*, Γ(Y, -))`, that is, `f_*` carries injective sheaves of abelian groups to
  `Γ(Y, -)`-acyclic sheaves.
* `exists_spectralSequence_sectionsFunctor_comp_pushforward`: the Leray spectral sequence
  `H^p(Y, R^q f_* K) ⇒ H^{p+q}(X, K)` for sheaves of abelian groups.
* `FirstQuadrantAbutment.mono_inflation`,
  `FirstQuadrantAbutment.exact_inflation_restriction`,
  `FirstQuadrantAbutment.exact_restriction_d` and
  `FirstQuadrantAbutment.exact_d_transgression`: the five term exact sequence in low degrees
  of a first quadrant `E₂` cohomological spectral sequence.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Leray

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of abelian groups on a topological space, presented as sheaves for the
open-cover topology on the poset of open subsets. -/
abbrev AbelianSheaf (X : TopCat.{u}) :=
  Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- The functor `Γ(U, -)` of sections of a sheaf of abelian groups over an open subset `U`. -/
noncomputable abbrev sectionsFunctor (X : TopCat.{u}) (U : Opens X) :
    AbelianSheaf X ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)

/-- Taking sections over an open subset is an additive functor. -/
instance sectionsFunctor_additive (X : TopCat.{u}) (U : Opens X) :
    (sectionsFunctor X U).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The direct image `f_*` of sheaves of abelian groups along a continuous map, given on
sections by `(f_*F)(V) = F(f^{-1}V)`. -/
noncomputable abbrev pushforward : AbelianSheaf X ⥤ AbelianSheaf Y :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The inverse image `f^{-1}` of sheaves of abelian groups along a continuous map: the chosen
left adjoint of the direct image. -/
noncomputable abbrev inverseImage : AbelianSheaf Y ⥤ AbelianSheaf X :=
  (Opens.map f).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The adjunction `f^{-1} ⊣ f_*` for sheaves of abelian groups. -/
noncomputable def inverseImagePushforwardAdjunction : inverseImage f ⊣ pushforward f :=
  (Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The inverse image of sheaves of abelian groups is left exact. -/
instance preservesFiniteLimits_inverseImage : PreservesFiniteLimits (inverseImage f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat ..

/-- **The direct image of sheaves of abelian groups preserves injective objects.** -/
instance pushforward_preservesInjectiveObjects :
    (pushforward f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inverseImagePushforwardAdjunction f)

/-- The direct image of sheaves of abelian groups is an additive functor. -/
instance pushforward_additive : (pushforward f).Additive where
  map_add := by intros; rfl

/-- Global sections on `X` are global sections on `Y` of the direct image:
`Γ(Y, -) ∘ f_* = Γ(X, -)`. -/
theorem pushforward_comp_sectionsFunctor :
    pushforward f ⋙ sectionsFunctor Y ⊤ = sectionsFunctor X ⊤ :=
  rfl

end

/-- **An injective object is right acyclic for every additive functor.** -/
theorem rightAcyclic_of_injective {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A] (I : A) (hI : Injective I) : F.rightAcyclic I := by
  have : ∀ m : ℤ, Injective (((HomotopyCategory.Plus.singleFunctor A 0).obj I).obj.as.X m) := by
    intro m
    exact inferInstanceAs
      (Injective (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj I).X m))
  show IsIso _
  infer_instance

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The direct image of an injective sheaf of abelian groups on `X` is right acyclic for
`Γ(Y, -)`. -/
theorem rightAcyclic_pushforward_obj_of_injective (I : AbelianSheaf X) (hI : Injective I) :
    (sectionsFunctor Y ⊤).rightAcyclic ((pushforward f).obj I) :=
  rightAcyclic_of_injective _ _ ((pushforward f).injective_obj_of_injective hI)

/-- **The Leray spectral sequence for sheaves of abelian groups.** Let `f : X ⟶ Y` be a
continuous map of topological spaces and let `K` be an object of `D⁺(Sh(X, Ab))`. There is a
filtered complex `L` of abelian groups with `H^n(L) ≅ H^n(X, K)` for all `n`, whose spectral
sequence `E`, presented as in [Stacks, Tag 012M] by its pages `Z_r^{p,q}/D_r^{p,q}`, has
`E_2^{p,q} ≅ H^p(Y, R^q f_* K)`, is bounded, induces a finite filtration on each `H^n(L)`, and
converges to `H^*(L)`. -/
theorem exists_spectralSequence_sectionsFunctor_comp_pushforward
    (K : DerivedCategory.Plus (AbelianSheaf X)) :
    ∃ L : FilteredObject (CochainComplex AddCommGrpCat.{u} ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (L.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
          ((sectionsFunctor X ⊤).rightDerivedFunctorPlus.obj K))) ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((L.filtration.ι.app (op p)).f n))
        (Z : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, Z r p n =
          Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (D : ∀ (_r _p n : ℤ), Subobject (L.X.X n))
        (_ : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (L.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (L.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (L.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{u} 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          ((sectionsFunctor Y ⊤).rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf Y) q).obj
              ((pushforward f).rightDerivedFunctorPlus.obj K)))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (L.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (L.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (L.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (L.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  obtain ⟨L, hL, -, hE⟩ :=
    CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp
      (pushforward f) (sectionsFunctor Y ⊤) (rightAcyclic_pushforward_obj_of_injective f) K
  exact ⟨L, hL, hE⟩

end

section FirstQuadrant

variable {C : Type*} [Category* C] [Abelian C]

/-- The cokernel of a morphism whose source is a zero object is its target. -/
noncomputable def cokernelIsoTargetOfIsZeroSrc {Z W : C} (g : Z ⟶ W) (hZ : IsZero Z) :
    cokernel g ≅ W :=
  cokernelIsoOfEq (hZ.eq_zero_of_src g) ≪≫ cokernelZeroIsoTarget

/-- Convergence data for a first quadrant `E₂` cohomological spectral sequence `E` and a
graded object `H`: a finite decreasing filtration
`H^n = F^0H^n ⊇ F^1H^n ⊇ ⋯ ⊇ F^{n+1}H^n = 0` of each `H^n` whose graded pieces are the terms
of the infinity page of `E`, `gr^pH^{p+q} = E_∞^{p,q}`. -/
@[ega "0 11.1.1" "(e), special case"]
structure FirstQuadrantAbutment (E : CohomologicalSpectralSequenceNat C 2) (H : ℕ → C) where
  /-- The filtration step `F^pH^n`. -/
  obj (n p : ℕ) : C
  /-- The inclusion `F^{p+1}H^n ⟶ F^pH^n` of one filtration step into the previous one. -/
  ι (n p : ℕ) : obj n (p + 1) ⟶ obj n p
  /-- The filtration is decreasing: each step is a subobject of the previous one. -/
  mono_ι (n p : ℕ) : Mono (ι n p)
  /-- The filtration of `H^n` starts at the whole of `H^n`. -/
  topIso (n : ℕ) : obj n 0 ≅ H n
  /-- The filtration of `H^n` has reached zero at the step `n + 1`. -/
  isZero_bot (n : ℕ) : IsZero (obj n (n + 1))
  /-- The graded pieces of the filtration are the terms of the infinity page. -/
  gradedIso (p q : ℕ) : E.pageInfinity (p, q) ≅ cokernel (ι (p + q) p)

namespace FirstQuadrantAbutment

variable {E : CohomologicalSpectralSequenceNat C 2} {H : ℕ → C} (D : FirstQuadrantAbutment E H)

/-- The last nonzero step `F^nH^n` of the filtration of `H^n` is the term `E_∞^{n,0}` of the
infinity page. -/
noncomputable def topGradedIso (n : ℕ) : E.pageInfinity (n, 0) ≅ D.obj n n :=
  D.gradedIso n 0 ≪≫ cokernelIsoTargetOfIsZeroSrc _ (D.isZero_bot n)

section

variable (E)

/-- In a first quadrant `E₂` spectral sequence every differential into `(0, 1)` vanishes on the
second page. -/
instance hasEdgeMonoAt_zero_one : E.HasEdgeMonoAt (0, 1) 2 :=
  CohomologicalSpectralSequenceNat.hasEdgeMonoAt _ _ _

/-- In a first quadrant `E₂` spectral sequence every differential out of `(2, 0)` vanishes on
the second page. -/
instance hasEdgeEpiAt_two_zero : E.HasEdgeEpiAt (2, 0) 2 :=
  CohomologicalSpectralSequenceNat.hasEdgeEpiAt _ _ _

/-- In a first quadrant `E₂` spectral sequence every differential into `(0, 1)` vanishes from
the third page on. -/
instance hasEdgeMonoAtFrom_zero_one : E.HasEdgeMonoAtFrom (0, 1) 3 :=
  CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom _ _ _

/-- In a first quadrant `E₂` spectral sequence every differential out of `(2, 0)` vanishes from
the third page on. -/
instance hasEdgeEpiAtFrom_two_zero : E.HasEdgeEpiAtFrom (2, 0) 3 :=
  CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom _ _ _

/-- The edge monomorphism `E_∞^{0,1} ⟶ E_2^{0,1}` is killed by the differential out of
`(0, 1)`. -/
theorem edgeMono_comp_d : E.edgeMono (0, 1) 2 ≫ (E.page 2).d (0, 1) (2, 0) = 0 := by
  rw [← E.pageInfinityIso_hom_edgeMonoStep' (0, 1) 2 3, Category.assoc,
    E.edgeMonoStep_comp_d (0, 1) (2, 0) 2 3, comp_zero]

/-- The edge epimorphism `E_2^{2,0} ⟶ E_∞^{2,0}` kills the differential into `(2, 0)`. -/
theorem d_comp_edgeEpi : (E.page 2).d (0, 1) (2, 0) ≫ E.edgeEpi (2, 0) 2 = 0 := by
  rw [← E.edgeEpiStep_pageInfinityIso_inv' (2, 0) 2 3 (by lia), ← Category.assoc,
    E.d_comp_edgeEpiStep (0, 1) (2, 0) 2 3, zero_comp]

end

/-- The **inflation** `E_2^{1,0} ⟶ H^1`: the identification of `E_2^{1,0}` with the graded
piece `gr^1H^1 = F^1H^1` followed by the inclusion `F^1H^1 ⊆ H^1`. -/
noncomputable def inflation : (E.page 2).X (1, 0) ⟶ H 1 :=
  E.edgeEpi (1, 0) 2 ≫ (D.topGradedIso 1).hom ≫ D.ι 1 0 ≫ (D.topIso 1).hom

/-- The **restriction** `H^1 ⟶ E_2^{0,1}`: the projection onto the graded piece
`gr^0H^1 = H^1/F^1H^1 = E_∞^{0,1}` followed by the edge monomorphism into `E_2^{0,1}`. -/
noncomputable def restriction : H 1 ⟶ (E.page 2).X (0, 1) :=
  (D.topIso 1).inv ≫ cokernel.π (D.ι 1 0) ≫ (D.gradedIso 0 1).inv ≫ E.edgeMono (0, 1) 2

/-- The **transgression** `E_2^{2,0} ⟶ H^2`: the edge epimorphism onto `E_∞^{2,0}`, which is
the graded piece `gr^2H^2 = F^2H^2`, followed by the inclusion `F^2H^2 ⊆ H^2`. -/
noncomputable def transgression : (E.page 2).X (2, 0) ⟶ H 2 :=
  E.edgeEpi (2, 0) 2 ≫ (D.topGradedIso 2).hom ≫ D.ι 2 1 ≫ D.ι 2 0 ≫ (D.topIso 2).hom

/-- The inflation is a monomorphism. -/
theorem mono_inflation : Mono D.inflation := by
  have : IsIso (E.edgeMono (1, 0) 2) := by
    rw [E.edgeMono_eq_pageInfinityIso_hom]; infer_instance
  have : IsIso (E.edgeEpi (1, 0) 2) := by
    rw [E.edgeEpi_eq_pageInfinityIso_inv]; infer_instance
  have := D.mono_ι 1 0
  rw [inflation]
  infer_instance

/-- The inflation followed by the restriction vanishes. -/
theorem inflation_restriction : D.inflation ≫ D.restriction = 0 := by
  simp [inflation, restriction]

/-- The restriction followed by the differential `d_2^{0,1}` vanishes. -/
theorem restriction_d : D.restriction ≫ (E.page 2).d (0, 1) (2, 0) = 0 := by
  simp only [restriction, Category.assoc, edgeMono_comp_d, comp_zero]

/-- The differential `d_2^{0,1}` followed by the transgression vanishes. -/
theorem d_transgression : (E.page 2).d (0, 1) (2, 0) ≫ D.transgression = 0 := by
  simp only [transgression, ← Category.assoc, d_comp_edgeEpi, zero_comp]

/-- **Exactness of the five term sequence at `H^1`.** -/
theorem exact_inflation_restriction :
    (ShortComplex.mk D.inflation D.restriction D.inflation_restriction).Exact := by
  have := D.mono_ι 1 0
  have hiso : IsIso (E.edgeMono (1, 0) 2) := by
    rw [E.edgeMono_eq_pageInfinityIso_hom]; infer_instance
  have hid : ∀ {Z : C} (g : E.pageInfinity (1, 0) ⟶ Z),
      E.edgeMono (1, 0) 2 ≫ E.edgeEpi (1, 0) 2 ≫ g = g := fun g => by
    rw [← Category.assoc, E.edgeMono_eq_pageInfinityIso_hom,
      E.edgeEpi_eq_pageInfinityIso_inv, Iso.hom_inv_id, Category.id_comp]
  have hS : (ShortComplex.mk (D.ι 1 0) (cokernel.π (D.ι 1 0)) (cokernel.condition _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  let φ : ShortComplex.mk (D.ι 1 0) (cokernel.π (D.ι 1 0)) (cokernel.condition _) ⟶
      ShortComplex.mk D.inflation D.restriction D.inflation_restriction :=
    ShortComplex.homMk ((D.topGradedIso 1).inv ≫ E.edgeMono (1, 0) 2) (D.topIso 1).hom
      ((D.gradedIso 0 1).inv ≫ E.edgeMono (0, 1) 2)
      (by simp only [inflation, Category.assoc, hid, Iso.inv_hom_id_assoc])
      (by simp only [restriction, Iso.hom_inv_id_assoc])
  have : Epi φ.τ₁ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS

/-- **Exactness of the five term sequence at `E_2^{0,1}`.** -/
theorem exact_restriction_d :
    (ShortComplex.mk D.restriction ((E.page 2).d (0, 1) (2, 0)) D.restriction_d).Exact := by
  have := D.mono_ι 1 0
  have hS := E.edgeMonoStepShortComplex_exact (0, 1) (2, 0) 2 3
    (ComplexShape.next_eq' _ ⟨by lia, by lia⟩)
  let φ : ShortComplex.mk D.restriction ((E.page 2).d (0, 1) (2, 0)) D.restriction_d ⟶
      E.edgeMonoStepShortComplex (0, 1) (2, 0) 2 3 :=
    ShortComplex.homMk ((D.topIso 1).inv ≫ cokernel.π (D.ι 1 0) ≫
        (D.gradedIso 0 1).inv ≫ (E.pageInfinityIso (0, 1) 3).hom) (𝟙 _) (𝟙 _)
      (by
        simp only [SpectralSequence.edgeMonoStepShortComplex_f, Category.assoc,
          E.pageInfinityIso_hom_edgeMonoStep' (0, 1) 2 3, restriction, Category.comp_id])
      (by simp)
  have : Epi φ.τ₁ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS

/-- **Exactness of the five term sequence at `E_2^{2,0}`.** -/
theorem exact_d_transgression :
    (ShortComplex.mk ((E.page 2).d (0, 1) (2, 0)) D.transgression D.d_transgression).Exact := by
  have := D.mono_ι 2 0
  have := D.mono_ι 2 1
  have hS := E.edgeEpiStepShortComplex_exact (0, 1) (2, 0) 2 3
    (ComplexShape.prev_eq' _ ⟨by lia, by lia⟩)
  let φ : E.edgeEpiStepShortComplex (0, 1) (2, 0) 2 3 ⟶
      ShortComplex.mk ((E.page 2).d (0, 1) (2, 0)) D.transgression D.d_transgression :=
    ShortComplex.homMk (𝟙 _) (𝟙 _)
      ((E.pageInfinityIso (2, 0) 3).inv ≫ (D.topGradedIso 2).hom ≫
        D.ι 2 1 ≫ D.ι 2 0 ≫ (D.topIso 2).hom)
      (by simp)
      (by
        simp only [SpectralSequence.edgeEpiStepShortComplex_g, Category.id_comp,
          transgression, ← E.edgeEpiStep_pageInfinityIso_inv' (2, 0) 2 3 (by lia),
          Category.assoc])
  have : Epi φ.τ₁ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : IsIso φ.τ₂ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  have : Mono φ.τ₃ := by dsimp [φ, ShortComplex.homMk]; infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS

end FirstQuadrantAbutment

end FirstQuadrant

end Stacks.Cohomology.Leray

end
