module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGA
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.PullbackCup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CanonicalCupProductBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionWedge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.TotalCupPairingLaws
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaGaussManin
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProductLinear
/-!
# The cohomology of the Hodge complex: the identification with Hodge cohomology

The summands `Ω^p[-p]` of the Hodge complex `ℋ = ⨁_p Ω^p[-p]`, the part of `ℋ` above a degree,
the identification `H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)` for `p + q = n`, and the resulting
identification `hodgeDgaEquiv : H^n(X, ℋ) ≅ H^n_{Hodge}(X/S)`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafOfModules.baseRingedSpace

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry ComplexShape
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct DirectSum Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

attribute [local instance] AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor
  AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor_obj

/-! ### The summands `Ω^p[-p]` of the Hodge complex -/

section Summands

/-- **The summand `Ω^p[-p]` of the Hodge complex**: its degree-`p` term `Ω^p` placed in degree
`p`. -/
abbrev hodgeSummand (p : ℕ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ :=
  (HomologicalComplex.single _ (up ℤ) (p : ℤ)).obj ((hodgeComplexInt B).X (p : ℤ))

/-- The degree-`p` term of the Hodge complex is `Ω^p`. -/
def hodgeComplexIntXIso (p : ℕ) : (hodgeComplexInt B).X (p : ℤ) ≅ deRhamTerm B p :=
  (deRhamComplex B (deRhamDifferential B)).extendXIso embeddingUpNat (i := p) rfl

/-- **The inclusion `Ω^p[-p] ⟶ ℋ`** of a summand of the Hodge complex. -/
def hodgeSummandι (p : ℕ) : hodgeSummand B p ⟶ hodgeComplexInt B :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) fun k _ => by
    rw [hodgeComplexInt_d]
    exact Limits.comp_zero

/-- **The projection `ℋ ⟶ Ω^p[-p]`** of the Hodge complex onto a summand. -/
def hodgeSummandπ (p : ℕ) : hodgeComplexInt B ⟶ hodgeSummand B p :=
  HomologicalComplex.mkHomToSingle (𝟙 _) fun k _ => by
    rw [hodgeComplexInt_d]
    exact Limits.zero_comp

/-- The projection onto a summand retracts its inclusion. -/
@[reassoc (attr := simp)]
theorem hodgeSummandι_π (p : ℕ) : hodgeSummandι B p ≫ hodgeSummandπ B p = 𝟙 _ := by
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, hodgeSummandι, hodgeSummandπ, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomToSingle_f, HomologicalComplex.id_f, Category.id_comp,
    Category.comp_id]
  exact Iso.hom_inv_id _

/-- The projection onto a summand kills the other summands. -/
theorem hodgeSummandι_π_of_ne {p p' : ℕ} (h : p' ≠ p) :
    hodgeSummandι B p' ≫ hodgeSummandπ B p = 0 :=
  HomologicalComplex.from_single_hom_ext
    ((HomologicalComplex.isZero_single_obj_X (up ℤ) (p : ℤ) ((hodgeComplexInt B).X (p : ℤ))
      (p' : ℤ) (by exact_mod_cast h)).eq_of_tgt _ _)

/-- In degree `p` the idempotent of `ℋ` attached to the summand `Ω^p[-p]` is the identity. -/
theorem hodgeSummandπ_ι_f_self (p : ℕ) :
    (hodgeSummandπ B p ≫ hodgeSummandι B p).f (p : ℤ) = 𝟙 _ := by
  rw [HomologicalComplex.comp_f, hodgeSummandι, hodgeSummandπ, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.mkHomToSingle_f, Category.id_comp, Category.comp_id]
  exact Iso.inv_hom_id _

/-- Outside degree `p` the idempotent of `ℋ` attached to the summand `Ω^p[-p]` vanishes. -/
theorem hodgeSummandπ_ι_f_of_ne (p : ℕ) {i : ℤ} (h : i ≠ (p : ℤ)) :
    (hodgeSummandπ B p ≫ hodgeSummandι B p).f i = 0 := by
  rw [HomologicalComplex.comp_f,
    (HomologicalComplex.isZero_single_obj_X (up ℤ) (p : ℤ) ((hodgeComplexInt B).X (p : ℤ)) i
      h).eq_of_tgt
      ((hodgeSummandπ B p).f i) 0, Limits.zero_comp]

end Summands

/-! ### The part of the Hodge complex above a degree -/

section Truncation

/-- The stupid truncation `σ^{≥ n + 1}ℋ` of the Hodge complex. -/
abbrev hodgeTrunc (n : ℤ) :
    CochainComplex
      (_root_.SheafOfModules.{u} (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A))
      ℤ :=
  (hodgeComplexInt B).stupidTrunc (embeddingUpIntGE (n + 1))

/-- The differential of `σ^{≥ n + 1}ℋ` vanishes. -/
theorem hodgeTrunc_d (n i j : ℤ) : (hodgeTrunc B n).d i j = 0 := by
  by_cases hi : ∃ k, (embeddingUpIntGE (n + 1)).f k = i
  · by_cases hj : ∃ k, (embeddingUpIntGE (n + 1)).f k = j
    · obtain ⟨k, hk⟩ := hi
      obtain ⟨l, hl⟩ := hj
      rw [HomologicalComplex.stupidTrunc_d_eq _ _ hk hl, hodgeComplexInt_d, Limits.zero_comp,
        Limits.comp_zero]
    · exact ((hodgeComplexInt B).isZero_stupidTrunc_X _ j
        (fun k hk => hj ⟨k, hk⟩)).eq_of_tgt _ _
  · exact ((hodgeComplexInt B).isZero_stupidTrunc_X _ i (fun k hk => hi ⟨k, hk⟩)).eq_of_src _ _

open Classical in
/-- The projection `ℋ ⟶ σ^{≥ n + 1}ℋ`, a map of complexes because the differential of `ℋ` is
zero. -/
def hodgeTruncπ (n : ℤ) : hodgeComplexInt B ⟶ hodgeTrunc B n where
  f i := if hi : ∃ k, (embeddingUpIntGE (n + 1)).f k = i then
      ((hodgeComplexInt B).stupidTruncXIso _ hi.choose_spec).inv else 0
  comm' i j _ := by rw [hodgeTrunc_d, hodgeComplexInt_d, Limits.comp_zero, Limits.zero_comp]

/-- The idempotent of `ℋ` attached to `σ^{≥ n + 1}ℋ`. -/
abbrev hodgeTruncIdem (n : ℤ) : hodgeComplexInt B ⟶ hodgeComplexInt B :=
  hodgeTruncπ B n ≫ (hodgeComplexInt B).ιStupidTrunc (embeddingUpIntGE (n + 1))

/-- In degrees `≥ n + 1` the idempotent attached to `σ^{≥ n + 1}ℋ` is the identity. -/
theorem hodgeTruncIdem_f_of_lt (n i : ℤ) (hi : n < i) : (hodgeTruncIdem B n).f i = 𝟙 _ := by
  have hk : (embeddingUpIntGE (n + 1)).f (i - (n + 1)).toNat = i := by
    change n + 1 + (((i - (n + 1)).toNat : ℕ) : ℤ) = i
    omega
  have h : ∃ k, (embeddingUpIntGE (n + 1)).f k = i := ⟨_, hk⟩
  rw [HomologicalComplex.comp_f, HomologicalComplex.ιStupidTrunc_f _ _ h.choose_spec]
  simp only [hodgeTruncπ, dite_eq_left h, Iso.inv_hom_id]

/-- In degrees `≤ n` the idempotent attached to `σ^{≥ n + 1}ℋ` vanishes. -/
theorem hodgeTruncIdem_f_of_le (n i : ℤ) (hi : i ≤ n) : (hodgeTruncIdem B n).f i = 0 := by
  have h : ¬ ∃ k, (embeddingUpIntGE (n + 1)).f k = i := by
    rintro ⟨k, hk⟩
    change n + 1 + (k : ℤ) = i at hk
    omega
  rw [HomologicalComplex.comp_f]
  simp only [hodgeTruncπ, dite_eq_right h, Limits.zero_comp]

/-- **The identity of `ℋ` splits**: it is the sum of the idempotents attached to the summands
`Ω^p[-p]` with `p ≤ n` and of the idempotent attached to `σ^{≥ n + 1}ℋ`. -/
theorem hodgeComplexInt_decomposition (n : ℤ) :
    (∑ p ∈ Finset.range (n + 1).toNat, hodgeSummandπ B p ≫ hodgeSummandι B p) +
      hodgeTruncIdem B n = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  rw [HomologicalComplex.add_f_apply, HomologicalComplex.id_f,
    ← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum]
  simp only [HomologicalComplex.Hom.fAddMonoidHom_apply]
  by_cases hneg : i < 0
  · exact (CochainComplex.isZero_of_isStrictlyGE (hodgeComplexInt B) 0 i hneg).eq_of_src _ _
  push Not at hneg
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hneg
  by_cases hk : (k : ℤ) ≤ n
  · rw [Finset.sum_eq_single k, hodgeSummandπ_ι_f_self, hodgeTruncIdem_f_of_le B n _ hk,
      add_zero]
    · intro p _ hp
      exact hodgeSummandπ_ι_f_of_ne B p (by exact_mod_cast (Ne.symm hp))
    · intro hk'
      exact absurd (Finset.mem_range.mpr (by omega)) hk'
  · push Not at hk
    rw [Finset.sum_eq_zero, hodgeTruncIdem_f_of_lt B n _ hk, zero_add]
    intro p hp
    exact hodgeSummandπ_ι_f_of_ne B p (by
      have := Finset.mem_range.mp hp
      omega)

/-- Derived global sections of sheaves of modules over the base ring sheaf carry an object
living in degrees `≥ n` to one living in degrees `≥ n`. -/
theorem isGE_derivedSectionsBase_obj
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))))
    (n : ℤ) (hK : K.IsGE n) :
    ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤).obj
      K).IsGE n :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE
    (Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen (baseRingedSpace A) ⊤)
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤)
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
    (fun I hI =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (Stacks.Cohomology.DerivedSectionsLeray.homotopySectionsOverOpen (baseRingedSpace A) ⊤)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
        (baseRingedSpace A))).2 DerivedCategory.Qh _ _ I hI) K n hK

/-- `H^n(X, σ^{≥ n + 1}ℋ) = 0`. -/
theorem isZero_cohomologyModule_hodgeTrunc (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((derivedSectionsBase A).obj (DerivedCategory.Q.obj (hodgeTrunc B n)))) :=
  DerivedCategory.isZero_of_isGE (hX := isGE_derivedSectionsBase_obj _ (n + 1) inferInstance) _
    (n + 1) n (by omega)

/-- The idempotent attached to `σ^{≥ n + 1}ℋ` acts by zero on `H^n(X, ℋ)`. -/
theorem cohomologyMap_hodgeTruncIdem (n : ℤ) :
    cohomologyMap (S := baseRingedSpace A) (hodgeTruncIdem B n) n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine (cohomologyMap_comp_apply (S := baseRingedSpace A) (hodgeTruncπ B n)
    ((hodgeComplexInt B).ιStupidTrunc (embeddingUpIntGE (n + 1))) n x).symm.trans ?_
  have hx : (cohomologyMap (S := baseRingedSpace A) (hodgeTruncπ B n) n).hom x = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomologyModule_hodgeTrunc B n)).elim _ _
  rw [hx, map_zero]
  rfl

end Truncation

/-! ### The cohomology of a summand -/

/-- The zero map of complexes induces the zero map on cohomology. -/
theorem cohomologyMap_zero {S : RingedSpace.{u, u}}
    {K K' : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (n : ℤ) : cohomologyMap (S := S) (0 : K ⟶ K') n = 0 := by
  have h2 := cohomologyMap_add (S := S) (0 : K ⟶ K') 0 n
  rw [add_zero] at h2
  simpa using h2

section SummandCohomology

/-- **`Ω^p[-p]` is the shift by `-p` of `Ω^p[0]`.** -/
def hodgeSummandShiftIso (p : ℕ) :
    hodgeSummand B p ≅
      shiftR (S := baseRingedSpace A) (singleInt (A := A) (deRhamTerm B p)) (-(p : ℤ)) :=
  (HomologicalComplex.single
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) (up ℤ)
      (p : ℤ)).mapIso (hodgeComplexIntXIso B p) ≪≫
    ((CochainComplex.singleFunctors
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))).shiftIso
        (-(p : ℤ)) (p : ℤ) 0 (by omega)).symm.app (deRhamTerm B p)

/-- **`H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)` for `p + q = n`**: the shift identification
`hodgeSummandShiftIso` followed by `H^n(X, Ω^p[0][-p]) ≅ H^{n - p}(X, Ω^p[0])`. -/
def hodgeSummandCohomologyIso (p : ℕ) (n q : ℤ) (h : -(p : ℤ) + n = q) :
    cohomologyModule (S := baseRingedSpace A)
        (DerivedCategory.Q.obj (hodgeSummand (A := A) B p)) n ≅
      hodgeComponentBase B p q :=
  (DerivedCategory.homologyFunctor _ n).mapIso ((baseSections (baseRingedSpace A)).mapIso
      (DerivedCategory.Q.mapIso (hodgeSummandShiftIso B p))) ≪≫
    shiftCohomologyIsoR (S := baseRingedSpace A) (singleInt (A := A) (deRhamTerm B p))
      (-(p : ℤ)) n q h

/-- The bidegrees of total degree `n`, as a finite set. -/
def hodgeBidegrees (n : ℤ) : Finset (HodgeBidegreeInt n) :=
  (Finset.range (n.toNat + 1) ×ˢ Finset.range (n.toNat + 1)).subtype
    fun i => ((i.1 + i.2 : ℕ) : ℤ) = n

/-- Every bidegree of total degree `n` lies in `hodgeBidegrees n`. -/
theorem mem_hodgeBidegrees {n : ℤ} (i : HodgeBidegreeInt n) : i ∈ hodgeBidegrees n := by
  rw [hodgeBidegrees, Finset.mem_subtype, Finset.mem_product, Finset.mem_range,
    Finset.mem_range]
  have := i.2
  omega

/-- The degree relation of a bidegree of total degree `n`. -/
theorem HodgeBidegreeInt.neg_add_eq {n : ℤ} (i : HodgeBidegreeInt n) :
    -((i.1.1 : ℕ) : ℤ) + n = ((i.1.2 : ℕ) : ℤ) := by
  have := i.2
  push_cast at this
  omega

/-- A morphism of modules over the ring `baseRing (baseRingedSpace A)` of global sections, read
as a morphism of modules over the same ring spelled `(underlyingRingSheaf A)(X)`. -/
abbrev baseHomToR {M N : ModuleCat.{u} (baseRing (baseRingedSpace A))} (f : M ⟶ N) :
    @Quiver.Hom (ModuleCat.{u} ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj
      (op ⊤))) _ M N :=
  f

/-- `H^n(X, -)` of a composite of maps of complexes. -/
theorem cohomologyMap_comp {S : RingedSpace.{u, u}}
    {K K' K'' : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (f : K ⟶ K') (g : K' ⟶ K'') (n : ℤ) :
    cohomologyMap (S := S) (f ≫ g) n = cohomologyMap (S := S) f n ≫ cohomologyMap (S := S) g n := by
  unfold cohomologyMap
  rw [DerivedCategory.Q.map_comp, Functor.map_comp, Functor.map_comp]

/-- `H^n(X, -)` of an identity. -/
theorem cohomologyMap_id {S : RingedSpace.{u, u}}
    (K : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (n : ℤ) : cohomologyMap (S := S) (𝟙 K) n = 𝟙 _ := by
  unfold cohomologyMap
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

/-- **The inclusion of a class of pure bidegree**
`H^q(X, Ω^p) ≅ H^n(X, Ω^p[-p]) ⟶ H^n(X, ℋ)`, for `p + q = n`, on cohomology modules. -/
def hodgeInclHom {n : ℤ} (i : HodgeBidegreeInt n) :
    hodgeComponentBase B i.1.1 (i.1.2 : ℤ) ⟶
      cohomologyModule (S := baseRingedSpace A)
        (DerivedCategory.Q.obj (hodgeComplexInt (A := A) B)) n :=
  (hodgeSummandCohomologyIso B i.1.1 n i.1.2 i.neg_add_eq).inv ≫
    cohomologyMap (S := baseRingedSpace A) (hodgeSummandι B i.1.1) n

/-- **The projection onto a pure bidegree**
`H^n(X, ℋ) ⟶ H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)`, for `p + q = n`, on cohomology modules. -/
def hodgeProjHom {n : ℤ} (i : HodgeBidegreeInt n) :
    cohomologyModule (S := baseRingedSpace A)
        (DerivedCategory.Q.obj (hodgeComplexInt (A := A) B)) n ⟶
      hodgeComponentBase B i.1.1 (i.1.2 : ℤ) :=
  cohomologyMap (S := baseRingedSpace A) (hodgeSummandπ B i.1.1) n ≫
    (hodgeSummandCohomologyIso B i.1.1 n i.1.2 i.neg_add_eq).hom

/-- The composite of the inclusion of bidegree `i` and the projection onto bidegree `j` is induced
by the composite `ι_i ≫ π_j` of maps of complexes. -/
private theorem hodgeInclHom_hodgeProjHom_eq {n : ℤ} (i j : HodgeBidegreeInt n) :
    hodgeInclHom B i ≫ hodgeProjHom B j =
      (hodgeSummandCohomologyIso B i.1.1 n i.1.2 i.neg_add_eq).inv ≫
        cohomologyMap (S := baseRingedSpace A) (hodgeSummandι B i.1.1 ≫ hodgeSummandπ B j.1.1) n ≫
          (hodgeSummandCohomologyIso B j.1.1 n j.1.2 j.neg_add_eq).hom := by
  rw [hodgeInclHom, hodgeProjHom, Category.assoc, ← Category.assoc (cohomologyMap _ n),
    ← cohomologyMap_comp]

/-- The projection onto a pure bidegree retracts the inclusion of that bidegree. -/
theorem hodgeInclHom_hodgeProjHom {n : ℤ} (i : HodgeBidegreeInt n) :
    hodgeInclHom B i ≫ hodgeProjHom B i = 𝟙 _ := by
  rw [hodgeInclHom_hodgeProjHom_eq, hodgeSummandι_π, cohomologyMap_id, Category.id_comp,
    Iso.inv_hom_id]

/-- The projection onto a pure bidegree kills the classes of the other bidegrees. -/
theorem hodgeInclHom_hodgeProjHom_of_ne {n : ℤ} {i j : HodgeBidegreeInt n} (hij : i ≠ j) :
    hodgeInclHom B i ≫ hodgeProjHom B j = 0 := by
  have hp : i.1.1 ≠ j.1.1 := by
    intro hp
    refine hij (Subtype.ext (Prod.ext hp ?_))
    have hi := i.2
    have hj := j.2
    push_cast at hi hj
    omega
  rw [hodgeInclHom_hodgeProjHom_eq, hodgeSummandι_π_of_ne B hp, cohomologyMap_zero,
    Limits.zero_comp, Limits.comp_zero]

/-- The idempotent of `H^n(X, ℋ)` attached to a bidegree `(p, q)` is induced by the idempotent
of `ℋ` attached to the summand `Ω^p[-p]`. -/
theorem hodgeProjHom_hodgeInclHom {n : ℤ} (i : HodgeBidegreeInt n) :
    hodgeProjHom B i ≫ hodgeInclHom B i = cohomologyMap (S := baseRingedSpace A)
      (hodgeSummandπ B i.1.1 ≫ hodgeSummandι B i.1.1) n := by
  rw [hodgeInclHom, hodgeProjHom, Category.assoc, Iso.hom_inv_id_assoc, ← cohomologyMap_comp]

/-- `H^n(X, -)` of a finite sum of maps of complexes. -/
theorem cohomologyMap_sum {S : RingedSpace.{u, u}}
    {K K' : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ}
    {ι : Type*} (s : Finset ι) (f : ι → (K ⟶ K')) (n : ℤ) :
    cohomologyMap (S := S) (∑ i ∈ s, f i) n = ∑ i ∈ s, cohomologyMap (S := S) (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cohomologyMap_zero (S := S) (K := K) (K' := K') n
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

/-- The sum over the bidegrees of total degree `n` of the idempotents of the summands, on
`H^n(X, ℋ)`, is the sum over the summands `Ω^p[-p]` with `p ≤ n`. -/
theorem sum_hodgeProjHom_hodgeInclHom_eq (n : ℤ) :
    ∑ i ∈ hodgeBidegrees n, hodgeProjHom B i ≫ hodgeInclHom B i =
      ∑ p ∈ Finset.range (n + 1).toNat, cohomologyMap (S := baseRingedSpace A)
        (hodgeSummandπ B p ≫ hodgeSummandι B p) n := by
  refine Finset.sum_bij' (fun i _ => i.1.1)
    (fun p hp => ⟨(p, (n - p).toNat), by
      have := Finset.mem_range.mp hp
      push_cast
      omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro i _
    have := i.2
    exact Finset.mem_range.mpr (by push_cast at this; omega)
  · intro p _
    exact mem_hodgeBidegrees _
  · intro i _
    refine Subtype.ext (Prod.ext rfl ?_)
    have := i.2
    push_cast at this ⊢
    omega
  · intro p _
    rfl
  · intro i _
    exact hodgeProjHom_hodgeInclHom B i

/-- **Every class of `H^n(X, ℋ)` is the sum of its components of pure bidegree.** -/
theorem sum_hodgeProjHom_hodgeInclHom (n : ℤ) :
    ∑ i ∈ hodgeBidegrees n, hodgeProjHom B i ≫ hodgeInclHom B i = 𝟙 _ := by
  have hdec := congrArg (fun f => cohomologyMap (S := baseRingedSpace A) f n)
    (hodgeComplexInt_decomposition B n)
  rw [cohomologyMap_add, cohomologyMap_sum, cohomologyMap_hodgeTruncIdem, add_zero,
    cohomologyMap_id] at hdec
  exact (sum_hodgeProjHom_hodgeInclHom_eq B n).trans hdec

/-- **The inclusion of a class of pure bidegree** `H^q(X, Ω^p) ⟶ H^n(X, ℋ)`, `p + q = n`. -/
abbrev hodgeIncl {n : ℤ} (i : HodgeBidegreeInt n) :
    hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) →ₗ[
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)]
      dgaCohomology (hodgeDGA B) n :=
  (baseHomToR (hodgeInclHom B i)).hom

/-- **The projection onto a pure bidegree** `H^n(X, ℋ) ⟶ H^q(X, Ω^p)`, `p + q = n`. -/
abbrev hodgeProj {n : ℤ} (i : HodgeBidegreeInt n) :
    dgaCohomology (hodgeDGA B) n →ₗ[
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)]
      hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) :=
  (baseHomToR (hodgeProjHom B i)).hom

/-- `hodgeInclHom_hodgeProjHom` on elements. -/
theorem hodgeProj_hodgeIncl_self {n : ℤ} (i : HodgeBidegreeInt n)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) : hodgeProj B i (hodgeIncl B i ξ) = ξ :=
  ConcreteCategory.congr_hom (hodgeInclHom_hodgeProjHom B i) ξ

/-- `hodgeInclHom_hodgeProjHom_of_ne` on elements. -/
theorem hodgeProj_hodgeIncl_of_ne {n : ℤ} {i j : HodgeBidegreeInt n} (hij : i ≠ j)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) : hodgeProj B j (hodgeIncl B i ξ) = 0 :=
  ConcreteCategory.congr_hom (hodgeInclHom_hodgeProjHom_of_ne B hij) ξ

/-- `sum_hodgeProjHom_hodgeInclHom` on elements. -/
theorem sum_hodgeIncl_hodgeProj (n : ℤ) (x : dgaCohomology (hodgeDGA B) n) :
    ∑ i ∈ hodgeBidegrees n, hodgeIncl B i (hodgeProj B i x) = x := by
  let ev : (cohomologyModule (S := baseRingedSpace A)
      (DerivedCategory.Q.obj (hodgeComplexInt (A := A) B)) n ⟶ cohomologyModule
        (S := baseRingedSpace A) (DerivedCategory.Q.obj (hodgeComplexInt (A := A) B)) n) →+
      dgaCohomology (hodgeDGA B) n :=
    { toFun := fun g => g.hom x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev (sum_hodgeProjHom_hodgeInclHom B n)
  rwa [map_sum] at h

end SummandCohomology

/-! ### The cohomology of the Hodge complex -/

section Equiv

/-- **`H^n(X, ℋ) ≅ H^n_{Hodge}(X/S)`.** The cohomology of the Hodge complex `ℋ = ⨁_p Ω^p[-p]` in
degree `n` is the direct sum of the Hodge cohomology groups `H^q(X, Ω^p)` with `p + q = n`: a class
goes to its components of pure bidegree. -/
def hodgeDgaEquiv (n : ℤ) :
    dgaCohomology (hodgeDGA B) n ≃ₗ[
        (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)]
      hodgePiece B n :=
  LinearEquiv.ofLinearMap
    (∑ i ∈ hodgeBidegrees n, (DirectSum.lof _ _ (fun i : HodgeBidegreeInt n =>
      (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) i).comp (hodgeProj B i))
    (DirectSum.toModule _ _ _ fun i => hodgeIncl B i)
    (by
      refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun ξ => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.toModule_lof, LinearMap.sum_apply,
        Finset.sum_eq_single k, LinearMap.comp_apply, hodgeProj_hodgeIncl_self]
      · rfl
      · intro j _ hj
        rw [LinearMap.comp_apply, hodgeProj_hodgeIncl_of_ne B (Ne.symm hj), map_zero]
      · exact fun hk => absurd (mem_hodgeBidegrees k) hk)
    (by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (sum_hodgeIncl_hodgeProj B n x)
      rw [LinearMap.comp_apply, DirectSum.toModule_lof])

/-- `hodgeDgaEquiv` on the image of a class of pure bidegree. -/
theorem hodgeDgaEquiv_hodgeIncl {n : ℤ} (i : HodgeBidegreeInt n)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) :
    hodgeDgaEquiv B n (hodgeIncl B i ξ) = DirectSum.of _ i ξ := by
  change (∑ j ∈ hodgeBidegrees n, (DirectSum.lof _ _ (fun i : HodgeBidegreeInt n =>
      (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) j).comp (hodgeProj B j))
    (hodgeIncl B i ξ) = _
  rw [LinearMap.sum_apply, Finset.sum_eq_single i, LinearMap.comp_apply, hodgeProj_hodgeIncl_self]
  · rfl
  · intro j _ hj
    rw [LinearMap.comp_apply, hodgeProj_hodgeIncl_of_ne B (Ne.symm hj), map_zero]
  · exact fun hi => absurd (mem_hodgeBidegrees i) hi

/-- **The inverse of `hodgeDgaEquiv` on a class of pure bidegree `(p, q)`** is its image under
the inclusion `Ω^p[-p] ⟶ ℋ`. -/
theorem hodgeDgaEquiv_symm_of {n : ℤ} (i : HodgeBidegreeInt n)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) :
    (hodgeDgaEquiv B n).symm (DirectSum.of _ i ξ) = hodgeIncl B i ξ := by
  rw [← (hodgeDgaEquiv B n).symm_apply_apply (hodgeIncl B i ξ), hodgeDgaEquiv_hodgeIncl]

end Equiv

end Stacks.HodgeWeil

end
