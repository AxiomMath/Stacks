module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.FreeBasis
public import StacksFrontier.RingTheory.Cech.KoszulColimit
public import StacksFrontier.RingTheory.Koszul.Semilinear
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The system of Koszul complexes on the powers of a family of sections

Let `O` be a presheaf of commutative rings on a category `C` and let `f₁, …, f_r` be a family of
sections of `O` available over every object, in the sense of `PresheafOfModules.Sequence`. For
every exponent there is a Koszul complex on the corresponding powers of that family, and this
file builds that system at the level of presheaves of modules and identifies it sectionwise with
the ring-level system of `StacksFrontier.RingTheory.Cech.KoszulColimit`.

The point of the identification is that it is an *equality of components*, not a transport: the
sections of the degree-`q` term of `PresheafOfModules.seqExteriorKoszulComplex` over an object
`U` are the exterior power `⋀^q_{O(U)}(O(U)^r)` on the nose, which is also the degree-`q` term of
`Koszul.seqComplex`. So the comparison isomorphism is the identity in every degree, and its only
content is that the two differentials agree — which they do by definition, both being contraction
by `Koszul.seqDual`.

## Main definitions

* `PresheafOfModules.Sequence.pow`: the family of `(n + 1)`-st powers of a family of sections.
* `PresheafOfModules.koszulPowerComplex`: **the Koszul complex on the `(n + 1)`-st powers of
  `f₁, …, f_r`**, as a chain complex of presheaves of modules.
* `PresheafOfModules.koszulPowerSectionsIso`: **the sectionwise identification** of that complex
  with the ring-level `Koszul.seqComplex` of the restricted powers.
* `PresheafOfModules.koszulPowerCochainSectionsIso`: the same identification read after the
  regrading of `Cech.koszulRegradingFunctor`, so that its target is literally
  `Cech.koszulPowerCochainComplex`.

## Main results

* `PresheafOfModules.Sequence.pow_restrict`: restricting the powers is taking the powers of the
  restrictions.
* `PresheafOfModules.koszulPowerSectionsIsoPow_hom_f`: that identification is the identity in
  every degree, so it carries no transport; and
  `PresheafOfModules.koszulPowerSectionsIsoPow_finFreeWedge` reads it on the standard exterior
  basis vectors, which is the shape `Cech.cechComplex_isColimit_koszulPowerComplexes` is stated in.
* `PresheafOfModules.koszulPowerComplex_restrict_val`: the restriction maps of the Koszul power
  complex are the semilinear base changes `ExteriorAlgebra.mapₛₗ` of the exterior algebra.
* `PresheafOfModules.koszulPower_contraction_naturality`: the ring-level Koszul differentials of
  the restricted powers commute with that semilinear base change.

Those last two together are **the naturality of the sectionwise identification in the object of
the site.** The identification is the identity in every degree, so its naturality square is the
first of them in each degree together with the second for the differentials; there is no further
transport to check.

## Implementation notes

The exponent `n` indexes the power `n + 1`, as in `Cech.koszulPowerCochainComplex`; this avoids a
separate convention for positive natural numbers.

`Sequence.pow` keeps the base object and the restriction morphisms of the original family and
only replaces its sections by their powers, so that `Sequence.pow_restrict` is `map_pow` and
nothing else.

Sections over a fixed object are taken with Mathlib's `PresheafOfModules.evaluation`, which is
already additive, so `Functor.mapHomologicalComplex` applies to it with nothing added here.

The comparison with `Cech.koszulPowerCochainComplex` is stated through the regrading functor
rather than by rebuilding the regrading for presheaves of modules. Reconstructing the regrading
one category at a time would require commuting the three functors it is composed of past the
sections functor; applying it to the already-established isomorphism of chain complexes needs
none of that.

## References

* [The Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [The Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped ExteriorAlgebra

universe v u w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}} {r : ℕ}

/-! ### The family of powers -/

/-- **The family of `(n + 1)`-st powers of a family of sections**, over the same base object and
with the same restriction morphisms. -/
noncomputable def Sequence.pow (f : Sequence O r) (n : ℕ) : Sequence O r where
  base := f.base
  elem i := f.elem i ^ (n + 1)
  res := f.res
  res_comp := f.res_comp

/-- The `i`-th section of the family of `(n + 1)`-st powers is `fᵢ ^ (n + 1)`. -/
@[simp]
theorem Sequence.pow_elem (f : Sequence O r) (n : ℕ) (i : Fin r) :
    (f.pow n).elem i = f.elem i ^ (n + 1) :=
  rfl

/-- **Restricting the powers is taking the powers of the restrictions.** -/
theorem Sequence.pow_restrict (f : Sequence O r) (n : ℕ) (U : Cᵒᵖ) (i : Fin r) :
    (f.pow n).restrict U i = f.restrict U i ^ (n + 1) := by
  rw [Sequence.restrict, Sequence.restrict]
  exact map_pow _ _ _

/-- The restriction to `U` of the family of `(n + 1)`-st powers is the family of `(n + 1)`-st
powers of the restrictions to `U`. -/
theorem Sequence.pow_restrict_eq (f : Sequence O r) (n : ℕ) (U : Cᵒᵖ) :
    (f.pow n).restrict U = fun i => f.restrict U i ^ (n + 1) :=
  funext fun i => f.pow_restrict n U i

/-! ### The Koszul complex on the powers -/

/-- **The Koszul complex on the `(n + 1)`-st powers of a family of sections `f₁, …, f_r`**, as a
chain complex of presheaves of `O`-modules. In degree `q` it is the presheaf of sectionwise
exterior powers `U ↦ ⋀^q_{O(U)}(O(U)^r)`, and its differential is contraction by the functional
`v ↦ ∑ i, vᵢ fᵢ^{n+1}`. -/
@[ega "III 1.1.1" "more general", sga "3 III 4.6.1" "more general"]
noncomputable def koszulPowerComplex (f : Sequence O r) (n : ℕ) :
    ChainComplex (PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)) ℕ :=
  seqExteriorKoszulComplex (f.pow n)

/-- The degree-`q` term of `koszulPowerComplex f n` is the presheaf of degree-`q` exterior powers
of `finFree O r`. -/
@[simp]
theorem koszulPowerComplex_X (f : Sequence O r) (n q : ℕ) :
    (koszulPowerComplex f n).X q = exteriorAlgebraPiece (q : ℤ) (finFree O r) :=
  rfl

/-- The differential of `koszulPowerComplex f n` from degree `q + 1` to degree `q` is contraction
by the functional `seqExteriorFunctional (f.pow n)`. -/
theorem koszulPowerComplex_d (f : Sequence O r) (n q : ℕ) :
    (koszulPowerComplex f n).d (q + 1) q =
      exteriorKoszulD (finFree O r) (seqExteriorFunctional (f.pow n)) (q : ℤ) :=
  seqExteriorKoszulComplex_d (f.pow n) q

/-! ### The sectionwise identification with the ring-level Koszul complex -/

/-- **The sectionwise identification of the Koszul power complex with the ring-level one.** Over
an object `U` the degree-`q` term of `koszulPowerComplex f n` has sections `⋀^q_{O(U)}(O(U)^r)`,
which is the degree-`q` term of the Koszul complex of the sequence `f₁|_U^{n+1}, …, f_r|_U^{n+1}`;
the isomorphism is the identity in every degree, and the two differentials agree because both are
contraction by `Koszul.seqDual` of that sequence. -/
noncomputable def koszulPowerSectionsIsoPow (f : Sequence O r) (n : ℕ) (U : Cᵒᵖ) :
    ((evaluation (O ⋙ forget₂ _ RingCat) U).mapHomologicalComplex _).obj (koszulPowerComplex f n) ≅
      Koszul.seqComplex ((f.pow n).restrict U) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : j + 1 = i := hij
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, koszulPowerComplex_d,
      Koszul.seqComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext rfl))

/-- **The sectionwise identification of the Koszul power complex with the ring-level one**, with
the sequence of powers written as the powers of the restricted sequence, which is the spelling
`Cech.koszulPowerCochainComplex` uses. -/
noncomputable def koszulPowerSectionsIso (f : Sequence O r) (n : ℕ) (U : Cᵒᵖ) :
    ((evaluation (O ⋙ forget₂ _ RingCat) U).mapHomologicalComplex _).obj (koszulPowerComplex f n) ≅
      Koszul.seqComplex (fun i => f.restrict U i ^ (n + 1)) :=
  (koszulPowerSectionsIsoPow f n U).trans (eqToIso (by rw [f.pow_restrict_eq n U]))

/-- **The sectionwise identification, read after the regrading.** The target is literally
`Cech.koszulPowerCochainComplex` of the restricted family: the cochain complex that
`Cech.cechComplex_isColimit_koszulPowerComplexes` exhibits the extended alternating Čech complex
as the colimit of. -/
noncomputable def koszulPowerCochainSectionsIso (f : Sequence O r) (n : ℕ) (U : Cᵒᵖ) :
    (Cech.koszulRegradingFunctor _ r).obj
        (((evaluation (O ⋙ forget₂ _ RingCat) U).mapHomologicalComplex _).obj
          (koszulPowerComplex f n)) ≅
      Cech.koszulPowerCochainComplex (f.restrict U) n :=
  (Cech.koszulRegradingFunctor _ r).mapIso (koszulPowerSectionsIso f n U)

/-- **The sectionwise identification is the identity in every degree.** There is no transport in
it: the sections of the degree-`q` term and the degree-`q` term of the ring-level Koszul complex
are the same module, and the isomorphism only records that the differentials agree. -/
@[simp]
theorem koszulPowerSectionsIsoPow_hom_f (f : Sequence O r) (n q : ℕ) (U : Cᵒᵖ) :
    (koszulPowerSectionsIsoPow f n U).hom.f q = 𝟙 _ :=
  rfl

/-- **The identification on the standard exterior basis vectors.** A wedge of standard basis
sections of `finFree O r` is the element of `⋀^q_{O(U)}(O(U)^r)` that
`Cech.cechComplex_isColimit_koszulPowerComplexes` is stated on. -/
theorem koszulPowerSectionsIsoPow_finFreeWedge (f : Sequence O r) (n q : ℕ) (U : Cᵒᵖ)
    (i : Fin q → Fin r) :
    (koszulPowerSectionsIsoPow f n U).hom.f q (finFreeWedge O r q U i) =
      ⟨ExteriorAlgebra.ιMulti ((O ⋙ forget₂ CommRingCat RingCat).obj U) q
          (fun k => finFreeSingle O r U (i k)), Koszul.ιMulti_mem q _⟩ :=
  Subtype.ext rfl

/-! ### Naturality -/

/-- **The restriction maps of the Koszul power complex are the semilinear base changes of the
exterior algebra.** This is what makes the sectionwise identification natural: the identification
is the identity on components, so its naturality square is this equation together with
`koszulPower_contraction_naturality`. -/
theorem koszulPowerComplex_restrict_val (f : Sequence O r) (n q : ℕ) {U V : Cᵒᵖ} (φ : U ⟶ V)
    (x : ((koszulPowerComplex f n).X q).obj U) :
    exteriorAlgebraPieceVal (q : ℤ) (finFree O r) V
        (((koszulPowerComplex f n).X q).map φ x) =
      ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ CommRingCat RingCat).map φ).hom
        ((finFree O r).restrictₛₗ φ)
        (exteriorAlgebraPieceVal (q : ℤ) (finFree O r) U x) :=
  rfl

/-- **The ring-level Koszul differentials of the restricted powers commute with the semilinear
base change.** The functionals of the two stages are compatible because restriction is a ring map
and the family restricts to the family; so this is `Koszul.mapₛₗ_contraction`. -/
theorem koszulPower_contraction_naturality (f : Sequence O r) (n : ℕ) {U V : Cᵒᵖ} (φ : U ⟶ V)
    (a : ExteriorAlgebra ((O ⋙ forget₂ CommRingCat RingCat).obj U)
      (Fin r → ((O ⋙ forget₂ CommRingCat RingCat).obj U : Type w))) :
    ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ CommRingCat RingCat).map φ).hom
        ((finFree O r).restrictₛₗ φ)
        (Koszul.contraction (Koszul.seqDual (fun i => f.restrict U i ^ (n + 1))) a) =
      Koszul.contraction (Koszul.seqDual (fun i => f.restrict V i ^ (n + 1)))
        (ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ CommRingCat RingCat).map φ).hom
          ((finFree O r).restrictₛₗ φ) a) := by
  refine Koszul.mapₛₗ_contraction _ _ _ _ (fun v => ?_) a
  rw [← f.pow_restrict_eq n U, ← f.pow_restrict_eq n V]
  exact seqDual_restrict_naturality (f.pow n) φ v

end PresheafOfModules

end
