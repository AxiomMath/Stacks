module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Basic
import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# The category of schemes cut off at a cardinal

For a set `S₀` of schemes, Stacks 000J chooses a limit ordinal `α` such that the full
subcategory `Sch_α ⊆ Sch` of schemes lying in `V_α` contains `S₀`, is closed under passing to
any scheme of size at most `Bound(size S)` for `S ∈ Sch_α`, and computes countable limits and
colimits as they are computed in `Sch`. Stacks 000R lists further constructions under which
`Sch_α` is closed.

Here `Sch_α` is modelled by the cardinal invariant `AlgebraicGeometry.Scheme.size`: a scheme `S`
is an object of `Sch_κ` when `size S < κ`. Since `size` is an isomorphism invariant
(`Scheme.size_congr`), "there exists `S' ∈ Ob(Sch_α)` with `T ≅ S'`" becomes `size T < κ`, and
since `Sch_κ` is a full subcategory of `Sch`, a limit formed in `Sch` whose size is below `κ` is
a limit in `Sch_κ`. The conditions on `κ` are `ℵ₀ < κ`, `Cardinal.IsStrongPrelimit κ` (closure
under `Bound`) and `ℵ₀ < κ.ord.cof` (closure under countable suprema); each result assumes only
the ones it uses.

## Main results

* `AlgebraicGeometry.exists_size_cutoff`: for every set `S₀` of schemes there is a cardinal `κ`
  with `ℵ₀ < κ`, `Cardinal.IsStrongPrelimit κ` and `ℵ₀ < κ.ord.cof` such that `Sch_κ` contains
  `S₀`.
* `AlgebraicGeometry.Scheme.size_lt_of_le_stacksBound`: a scheme of size at most
  `Bound(size S)` for some `S ∈ Sch_κ` lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_lt_of_le_stacksBound_iSup`: a scheme of size at most
  `Bound(⨆ i, size (F i))`, for an at most countable family `F` in `Sch_κ`, lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_pullback_lt`: `Sch_κ` is closed under fibre products.
* `AlgebraicGeometry.Scheme.size_sigmaObj_lt`: `Sch_κ` is closed under at most countable
  coproducts.
* `AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`,
  `AlgebraicGeometry.Scheme.size_lt_of_isClosedImmersion`: the source of an open or closed
  immersion into an object of `Sch_κ` lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`: the same for
  finite type morphisms.
* `AlgebraicGeometry.Scheme.size_lt_of_openCover`: a scheme with an open covering whose index
  type and members are bounded by `size(T) ^ ℵ₀` for some `T ∈ Sch_κ` lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_affineCover`: the source of a
  morphism locally of finite type into an object of `Sch_κ`, with a small affine open covering,
  lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_lt_of_mono_quasiCompact`,
  `AlgebraicGeometry.Scheme.size_lt_of_mono_locallyOfFinitePresentation`: the same for
  quasi-compact monomorphisms and monomorphisms locally of finite presentation.
* `AlgebraicGeometry.Scheme.size_lt_of_isAffine_of_mk_le`,
  `AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le`: an affine scheme whose ring has cardinality
  at most `size(T) ^ ℵ₀` for some `T ∈ Sch_κ` lies in `Sch_κ`.
* `AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType`,
  `AlgebraicGeometry.Scheme.size_Spec_lt_of_isLocalization`,
  `AlgebraicGeometry.Scheme.size_Spec_lt_of_subring`: for `Spec R` in `Sch_κ`, the spectra of a
  finite type `R`-algebra, of a localization of `R` and of a subring of `R` lie in `Sch_κ`.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal Ordinal

universe u

namespace AlgebraicGeometry

/-- For every set `S₀` of schemes there is an uncountable strong limit cardinal `κ` of uncountable
cofinality such that every member of `S₀` has size below `κ`, that is, the collection
`Sch_κ = {S | size S < κ}` contains `S₀`. -/
@[stacks 000J]
theorem exists_size_cutoff (S₀ : Set Scheme.{u}) [Small.{u} S₀] :
    ∃ κ : Cardinal.{u}, ℵ₀ < κ ∧ Cardinal.IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof ∧
      ∀ S ∈ S₀, S.size < κ := by
  obtain ⟨κ, hμκ, hsl, hcof⟩ :=
    Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof
      (max ℵ₀ (⨆ S : S₀, (S : Scheme.{u}).size))
  refine ⟨κ, (le_max_left _ _).trans_lt hμκ, hsl, hcof, fun S hS => ?_⟩
  exact ((le_ciSup (f := fun S : S₀ => (S : Scheme.{u}).size) Cardinal.bddAbove_of_small
    ⟨S, hS⟩).trans (le_max_right _ _)).trans_lt hμκ

/-- If `S` is an object of `Sch_κ` and `T` is a scheme of size at most `Bound(size S)`, then `T` is
an object of `Sch_κ`. -/
@[stacks 000J "(2)"]
theorem Scheme.size_lt_of_le_stacksBound {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {S T : Scheme.{u}} (hS : S.size < κ)
    (hT : T.size ≤ Cardinal.stacksBound S.size) : T.size < κ :=
  lt_of_le_of_lt hT (Cardinal.stacksBound_lt_of_isStrongPrelimit hκ hsl hS)

/-- Let `F` be an at most countable family of objects of `Sch_κ`. Then every scheme of size at most
`Bound(⨆ i, size (F i))` is an object of `Sch_κ`. -/
@[stacks 000J "(3), (4)"]
theorem Scheme.size_lt_of_le_stacksBound_iSup {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof) {ι : Type u}
    (hι : #ι ≤ ℵ₀) (F : ι → Scheme.{u}) (hF : ∀ i, (F i).size < κ) {X : Scheme.{u}}
    (hX : X.size ≤ Cardinal.stacksBound (⨆ i, (F i).size)) : X.size < κ :=
  lt_of_le_of_lt hX
    (Cardinal.stacksBound_iSup_lt_of_isStrongPrelimit hκ hsl hcof hι _ hF)

end AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry

variable {κ : Cardinal.{u}}

/-! ### (1) Fibre products -/

/-- The fibre product of two objects of `Sch_κ` over any base, which need not lie in `Sch_κ`, is
again an object of `Sch_κ`. -/
@[stacks 000R "(1)"]
theorem Scheme.size_pullback_lt {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hX : X.size < κ) (hY : Y.size < κ) : (pullback f g).size < κ :=
  (Scheme.size_pullback_le f g).trans_lt (max_lt hX hY)

/-! ### (2) Countable coproducts -/

/-- If `κ` is uncountable of uncountable cofinality, the coproduct of an at most countable family
of objects of `Sch_κ` is again an object of `Sch_κ`. -/
@[stacks 000R "(2)"]
theorem Scheme.size_sigmaObj_lt (hκ : ℵ₀ < κ) (hcof : ℵ₀ < κ.ord.cof) {ι : Type u}
    (hι : #ι ≤ ℵ₀) (Y : ι → Scheme.{u}) (hY : ∀ i, (Y i).size < κ) : (∐ Y).size < κ :=
  (schemeSize_coproduct_le Y (max ℵ₀ (⨆ i, (Y i).size)) (le_max_left _ _)
    (hι.trans (le_max_left _ _)) fun j =>
      (le_ciSup Cardinal.bddAbove_of_small j).trans (le_max_right _ _)).trans_lt
    (max_lt hκ (iSup_lt_of_lt_cof_ord (hι.trans_lt hcof) hY))

/-! ### (8) Monomorphisms, and the immersions (3), (4) -/

/-- The morphism from the spectrum of a residue field is quasi-compact. -/
instance quasiCompact_fromSpecResidueField (X : Scheme.{u}) (x : X) :
    QuasiCompact (X.fromSpecResidueField x) :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun W _ =>
    (Set.toFinite (X.fromSpecResidueField x ⁻¹' (W : Set X))).isCompact

/-- The source of a quasi-compact monomorphism into an object of `Sch_κ` is an object of
`Sch_κ`. -/
@[stacks 000R "(8)"]
theorem Scheme.size_lt_of_mono_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    [QuasiCompact f] (hY : Y.size < κ) : X.size < κ :=
  (Scheme.size_le_of_mono_quasiCompact f).trans_lt hY

/-- The source of a monomorphism locally of finite presentation into an object of `Sch_κ` is an
object of `Sch_κ`. -/
@[stacks 000R "(8)"]
theorem Scheme.size_lt_of_mono_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Mono f] [LocallyOfFinitePresentation f] (hY : Y.size < κ) : X.size < κ :=
  (Scheme.size_le_of_mono_locallyOfFinitePresentation f).trans_lt hY

/-- The source of an open immersion into an object of `Sch_κ` is an object of `Sch_κ`. -/
@[stacks 000R "(3)"]
theorem Scheme.size_lt_of_isOpenImmersion {U S : Scheme.{u}} (f : U ⟶ S)
    [IsOpenImmersion f] (hS : S.size < κ) : U.size < κ :=
  Scheme.size_lt_of_mono_locallyOfFinitePresentation f hS

/-- The source of a closed immersion into an object of `Sch_κ` is an object of `Sch_κ`. -/
@[stacks 000R "(4)"]
theorem Scheme.size_lt_of_isClosedImmersion {T S : Scheme.{u}} (f : T ⟶ S)
    [IsClosedImmersion f] (hS : S.size < κ) : T.size < κ :=
  Scheme.size_lt_of_mono_quasiCompact f hS

/-! ### (6) Small open coverings -/

/-- Let `S` be a scheme with an open covering `S = ⋃ i, U i` and let `T` be an object of `Sch_κ`
such that the index type and every member of the covering are bounded by `size(T) ^ ℵ₀`. Then `S`
is an object of `Sch_κ`. -/
@[stacks 000R "(6)"]
theorem Scheme.size_lt_of_openCover (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {S : Scheme.{u}} {I : Type u} [Nonempty I] (U : I → S.Opens) (hcov : ⨆ i, U i = ⊤)
    {T : Scheme.{u}} (hT : T.size < κ) (hI : #I ≤ T.size ^ ℵ₀)
    (hU : ∀ i, (↑(U i) : Scheme.{u}).size ≤ T.size ^ ℵ₀) : S.size < κ :=
  ((Scheme.size_le_of_iSup_eq_top U hcov).trans (max_le hI (ciSup_le' hU))).trans_lt
    (power_aleph0_lt_of_isStrongPrelimit hκ hsl hT)

/-! ### (5) Finite type morphisms -/

/-- If `f : X ⟶ S` is locally of finite type and quasi-compact, then `size X ≤ size S`. -/
theorem Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] : X.size ≤ S.size := by
  have : Nonempty S.affineOpens := ⟨⟨⊥, isAffineOpen_bot S⟩⟩
  have hcov : ⨆ V : S.affineOpens, f ⁻¹ᵁ V.1 = ⊤ :=
    f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S)
  refine (Scheme.size_le_of_iSup_eq_top (fun V : S.affineOpens => f ⁻¹ᵁ V.1) hcov).trans
    (max_le (Scheme.mk_affineOpens_le_size S) (ciSup_le' fun V => ?_))
  have : IsAffine (↑V.1 : Scheme.{u}) := V.2
  have : CompactSpace (↑(f ⁻¹ᵁ V.1) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V.1)
  exact (Scheme.size_le_of_locallyOfFiniteType (f ∣_ V.1)).trans (Scheme.size_coe_opens_le S V.1)

/-- The source of a finite type morphism (locally of finite type and quasi-compact) into an object
of `Sch_κ` is an object of `Sch_κ`. -/
@[stacks 000R "(5)"]
theorem Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact {T S : Scheme.{u}} (f : T ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (hS : S.size < κ) : T.size < κ :=
  (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact f).trans_lt hS

/-! ### (7) Morphisms locally of finite type with a small affine covering -/

/-- Let `f : T ⟶ S` be locally of finite type with `S` an object of `Sch_κ`, and suppose `T` has an
affine open covering indexed by a type of cardinality at most `size(S) ^ ℵ₀`. Then `T` is an object
of `Sch_κ`. -/
@[stacks 000R "(7)"]
theorem Scheme.size_lt_of_locallyOfFiniteType_of_affineCover (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {T S : Scheme.{u}} (f : T ⟶ S)
    [LocallyOfFiniteType f] {I : Type u} [Nonempty I] (V : I → T.affineOpens)
    (hcov : ⨆ i, (V i).1 = ⊤) (hI : #I ≤ S.size ^ ℵ₀) (hS : S.size < κ) : T.size < κ := by
  refine Scheme.size_lt_of_openCover hκ hsl (fun i => (V i).1) hcov hS hI fun i => ?_
  have : IsAffine (↑(V i).1 : Scheme.{u}) := (V i).2
  exact (Scheme.size_le_of_locallyOfFiniteType ((V i).1.ι ≫ f)).trans
    (self_le_power _ one_le_aleph0)

/-! ### (9) Affine schemes and cardinality of rings -/

/-- An affine scheme `S` whose ring of global sections has cardinality at most
`Bound(size T) = size(T) ^ ℵ₀` for some object `T` of `Sch_κ` is itself an object of `Sch_κ`. -/
@[stacks 000R "(9)"]
theorem Scheme.size_lt_of_isAffine_of_mk_le (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {S T : Scheme.{u}} [IsAffine S] (hT : T.size < κ)
    (h : Cardinal.mk Γ(S, ⊤) ≤ T.size ^ ℵ₀) : S.size < κ :=
  (Scheme.size_of_isAffine S).trans_lt
    (max_lt hκ (h.trans_lt (power_aleph0_lt_of_isStrongPrelimit hκ hsl hT)))

/-- The ring of global sections of `Spec R` has the same cardinality as `R`. -/
private theorem mk_Γ_Spec (R : CommRingCat.{u}) : Cardinal.mk Γ(Spec R, ⊤) = Cardinal.mk R :=
  mk_congr (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toEquiv

/-- If `#R ≤ Bound(size T) = size(T) ^ ℵ₀` for some object `T` of `Sch_κ`, then `Spec R` is an
object of `Sch_κ`. -/
@[stacks 000R "(9)"]
theorem Scheme.size_Spec_lt_of_mk_le (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    (R : CommRingCat.{u}) {T : Scheme.{u}} (hT : T.size < κ)
    (h : Cardinal.mk R ≤ T.size ^ ℵ₀) : (Spec R).size < κ :=
  Scheme.size_lt_of_isAffine_of_mk_le hκ hsl hT
    (mk_Γ_Spec R ▸ h)

/-- The size of the spectrum of a ring `R` is `max {ℵ₀, #R}`. -/
theorem Scheme.size_Spec (R : CommRingCat.{u}) :
    (Spec R).size = max ℵ₀ (Cardinal.mk R) := by
  rw [Scheme.size_of_isAffine, mk_Γ_Spec]

/-- If `Spec R` is an object of `Sch_κ` and `#A ≤ max {ℵ₀, #R}`, then `Spec A` is an object of
`Sch_κ`. -/
theorem Scheme.size_Spec_lt_of_mk_le_max (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {R A : Type u} [CommRing R] [CommRing A]
    (hR : (Spec (CommRingCat.of R)).size < κ)
    (h : Cardinal.mk A ≤ max ℵ₀ (Cardinal.mk R)) : (Spec (CommRingCat.of A)).size < κ :=
  Scheme.size_Spec_lt_of_mk_le hκ hsl _ hR
    (h.trans ((Scheme.size_Spec _).symm.trans_le (self_le_power _ one_le_aleph0)))

/-- For an object `Spec R` of `Sch_κ` and a finite type `R`-algebra `A`, the scheme `Spec A` is an
object of `Sch_κ`. -/
@[stacks 000R "(9)(b)"]
theorem Scheme.size_Spec_lt_of_finiteType (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (hR : (Spec (CommRingCat.of R)).size < κ) :
    (Spec (CommRingCat.of A)).size < κ :=
  Scheme.size_Spec_lt_of_mk_le_max hκ hsl hR (mk_le_of_algebra_finiteType R A)

/-- For an object `Spec R` of `Sch_κ` and a localization `A` of `R` at a submonoid, the scheme
`Spec A` is an object of `Sch_κ`. -/
@[stacks 000R "(9)(c)"]
theorem Scheme.size_Spec_lt_of_isLocalization (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {R : Type u} [CommRing R] (M : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A]
    (hR : (Spec (CommRingCat.of R)).size < κ) : (Spec (CommRingCat.of A)).size < κ :=
  Scheme.size_Spec_lt_of_mk_le_max hκ hsl hR (mk_le_of_isLocalization M A)

/-- For an object `Spec R` of `Sch_κ` and a subring `R' ⊆ R`, the scheme `Spec R'` is an object of
`Sch_κ`. -/
@[stacks 000R "(9)(e)"]
theorem Scheme.size_Spec_lt_of_subring (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {R : Type u} [CommRing R] (R' : Subring R)
    (hR : (Spec (CommRingCat.of R)).size < κ) : (Spec (CommRingCat.of R')).size < κ :=
  Scheme.size_Spec_lt_of_mk_le_max hκ hsl hR
    ((mk_le_of_injective Subtype.val_injective).trans (le_max_right _ _))

end AlgebraicGeometry
