module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Topology.Sheaves.Flasque
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisDegreeOne
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing

/-!
# Vanishing of cohomology from Čech vanishing on a basis

Let `B` be a basis of open subsets of a space.  Stacks Tag 01EW asserts that if a cofinal
collection of covers by members of `B`, whose finite intersections also belong to `B`, has
vanishing positive-degree Čech cohomology, then higher sheaf cohomology vanishes on every member
of `B`.  `StacksDraft.Ch20.Sec11.Tag01EW` proves this modulo one hypothesis, the degree-one Čech
vanishing for the objects of cocycles `Zᵐ = ker(Iᵐ → Iᵐ⁺¹)` of an injective resolution of the
coefficients; this file discharges that hypothesis and proves the tag.

The hypothesis is *not* provable on its own: for `Zᵐ` with `m > 0` it needs the vanishing of
`Hᵐ` on the members of `B`, which is the conclusion of the tag in degree `m`.  The two are
therefore proved together, by induction on the degree: `isZero_Hobj_of_le` proves the tag up to
degree `n`, and its inductive step feeds the vanishing in degrees `≤ n` to the staircase
`cechSurjKer_of_le`, which produces the degree-one Čech vanishing for `Zⁿ`.

As in `StacksDraft.Ch20.Sec11.Tag01EW` the coefficients are generic: an abelian category `𝒜`
with enough injectives together with an exact functor `T` to the abelian sheaves on `X`.  Only
one further property of `T` is needed, `CechAcyclicInjectives T`: the sheaf underlying an
injective coefficient object has vanishing positive-degree Čech cohomology.  For sheaves of
modules this holds by Stacks 01EA followed by Stacks 09SZ, which is
`cechAcyclicInjectives_toSheaf`, and the resulting module-valued tag is
`isZero_hgroup_of_cech_isZero_on_basis`.  For abelian sheaves `T = 𝟭` and the acyclicity is
Stacks 09SZ directly; see `StacksDraft.Ch20.Sec11.Tag01EWAbelian`.

## Main definitions

* `Cochain Y P q` is a degree-`q` Čech cochain of the presheaf `P` of abelian groups for the
  family `Y` of open subsets; `comp` takes its components, `mk` builds a cochain from prescribed
  components and `dd` is the Čech differential.  `CechSurj Y P q` says that every Čech cocycle of
  degree `q + 1` is a Čech coboundary, the element form of the vanishing of Čech cohomology.
* `uliftFamily Y` is the family `Y` reindexed by a universe-lifted copy of its index type, and
  `cochainDown`, `cochainUp` are the induced identifications of cochains.
* `CechAcyclicInjectives T` is the one property of the coefficients used here beyond the
  exactness of `T`: injective objects have Čech-acyclic underlying sheaves.
* `secCochain T Y g` applies a morphism of coefficients to each component of a cochain.
* `CechSurjKer T Y dA q` is `CechSurj` for the kernel of `dA`, phrased for cochains with values
  in the source of `dA` all of whose components are killed by `dA`.

## Main results

* `cechSurj_of_injective` is the Čech acyclicity of an injective sheaf of modules: it is flasque
  by Tag 01EA, so Tag 09SZ applies to it; `cechAcyclicInjectives_toSheaf` packages it.
* `cechSurjKer_of_cechSurj` and `cechSurj_of_cechSurjKer` identify `CechSurj` for a kernel with
  `CechSurjKer`, in both directions.
* `exists_sec_eq_d_of_isZero` is the local lifting through the resolution: where `Hᵐ⁺¹(V, F)`
  vanishes, a section of `Iᵐ⁺¹` over `V` killed by the differential is a differential.
* `cechSurjKer_succ` is the staircase step and `cechSurjKer_of_le` the staircase.
* `isZero_Hobj_of_cech_isZero_on_basis` is Stacks Tag 01EW for an arbitrary category of
  coefficients, and `isZero_hgroup_of_cech_isZero_on_basis` is its case of sheaves of modules,
  which carries the tag.

## Implementation notes

Two universe constraints shape the file.  Tag 09SZ is stated for a family whose index type lives
in the universe of the coefficients, while the covers here are indexed by a type in the universe
of the space; the Čech cochain calculus is therefore set up for an index type in an arbitrary
universe — which `Stacks.Cohomology.Basis.cechMk` is not — and the family is reindexed along
`ULift` before Tag 09SZ is applied, which changes nothing because the intersection selected by a
tuple of lifted indices is literally the intersection selected by the underlying tuple.

The degree-`q` term of the Čech complex depends on the instance witnessing that the category of
abelian groups has products indexed by the index type of the family.  The family and the
coefficients are therefore explicit arguments of every operation on cochains: left implicit, that
instance gets resolved from an expected type before the index universe is known, which resolves
it at the wrong universe and leaves two definitionally equal types that no reasonable amount of
unfolding will identify.

Cochains with values in the object of `m`-cocycles are handled as cochains with values in `Iᵐ`
all of whose components are killed by the differential, rather than as cochains with values in
`HomologicalComplex.cycles`; the two are identified once, at the end, by
`cechSurj_of_cechSurjKer`.  This keeps the staircase free of the comparison maps between the
cocycle objects and makes the lifting step the plain exactness of the complex of sections.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis

-- `res_add` is simp from here, exactly as it was when this file declared it: the lemma itself now
-- lives in `OnABasisDegreeOne` alongside `res_id`/`res_sub`, but marking it simp there would widen
-- the attribute from this file's importers to all 3089 importers of that module.
attribute [simp] Stacks.Cohomology.Basis.res_add

universe u₂ v₂ t w v u

namespace Stacks.Cohomology.BasisCycles

noncomputable section

-- Mathlib v4.35.0: instance search for `HasProducts.{u} AddCommGrpCat.{max u w}` times out in
-- this file's environment; supply it directly from `AddCommGrpCat.hasLimitsOfShape`.
local instance hasProductsAddCommGrpCat : HasProducts.{u} AddCommGrpCat.{max u w} :=
  fun _ => AddCommGrpCat.hasLimitsOfShape

/-! ### Restriction of sections

The additivity of restriction, in the forms needed below;
`StacksDraft.Ch20.Sec11.Tag01EW` has the others. -/


/-! ### Čech cochains, componentwise

The componentwise calculus of Čech cochains, in the form used throughout this file: the index
type of the family is allowed to live in a universe unrelated to that of the space and to that
of the coefficients, which `Stacks.Cohomology.Basis.cechMk` does not allow and which the
reindexing along `ULift` below needs. -/

/-- Vanishing of a homology group of a complex of abelian groups, in element form. -/
private theorem isZero_homology_succ_iff {C : CochainComplex AddCommGrpCat.{v} ℕ} (m : ℕ) :
    IsZero (C.homology (m + 1)) ↔ ∀ z : ToType (C.X (m + 1)), C.d (m + 1) (m + 2) z = 0 →
      ∃ y : ToType (C.X m), C.d m (m + 1) y = z := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp)
      (by simp [CochainComplex.next]), ShortComplex.ab_exact_iff]
  rfl

section Cochains

variable {X : Type u} [TopologicalSpace X] {κ : Type t} (Y : κ → Opens X)
  (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) [HasProducts.{t} AddCommGrpCat.{v}]

/-- A degree-`q` Čech cochain of the presheaf `P` for the family `Y`. -/
abbrev Cochain (q : ℕ) : Type v := ToType (((cechComplexFunctor Y).obj P).X q)

omit [HasProducts.{t} AddCommGrpCat.{v}] in
/-- Reindexing a tuple enlarges the intersection it selects. -/
theorem inter_le_inter {m m' : ℕ} (x : Fin m → κ) (h : Fin m' → Fin m) :
    inter Y x ≤ inter Y (x ∘ h) :=
  leOfHom (interMap Y x h)

/-- The component of a Čech cochain at a tuple: a section of `P` over the intersection the
tuple selects. -/
def comp {q : ℕ} (s : Cochain Y P q) (y : Fin (q + 1) → κ) :
    ToType (P.obj (op (inter Y y))) :=
  ConcreteCategory.hom (π Y P q y) s

/-- The Čech cochain with prescribed components. -/
def mk {q : ℕ} (f : ∀ y : Fin (q + 1) → κ, ToType (P.obj (op (inter Y y)))) : Cochain Y P q :=
  ConcreteCategory.hom (lift Y P fun y => ofElt (f y)) (ULift.up 1)

/-- The components of `mk` are the prescribed sections. -/
@[simp]
theorem comp_mk {q : ℕ} (f : ∀ y : Fin (q + 1) → κ, ToType (P.obj (op (inter Y y))))
    (y : Fin (q + 1) → κ) : comp Y P (mk Y P f) y = f y := by
  rw [comp, mk, ← ConcreteCategory.comp_apply, lift_comp_π, ofElt_apply]

/-- Components at equal tuples, restricted to a common open, agree. -/
theorem res_comp_congr {q : ℕ} (s : Cochain Y P q) {y y' : Fin (q + 1) → κ} (hyy' : y = y')
    {W : Opens X} (h : W ≤ inter Y y) (h' : W ≤ inter Y y') :
    res P h (comp Y P s y) = res P h' (comp Y P s y') := by
  subst hyy'
  rfl

/-- A Čech cochain is determined by its components. -/
theorem cochain_ext {q : ℕ} (s t : Cochain Y P q) (h : ∀ y, comp Y P s y = comp Y P t y) :
    s = t :=
  eq_of_ofElt (Stacks.CategoryTheory.CechComplex.hom_ext Y P fun y => by
    rw [ofElt_comp, ofElt_comp]
    exact congrArg ofElt (h y))

/-- Taking components is additive. -/
@[simp]
theorem comp_add {q : ℕ} (s t : Cochain Y P q) (y : Fin (q + 1) → κ) :
    comp Y P (s + t) y = comp Y P s y + comp Y P t y := map_add _ _ _

/-- Taking components commutes with subtraction. -/
@[simp]
theorem comp_sub {q : ℕ} (s t : Cochain Y P q) (y : Fin (q + 1) → κ) :
    comp Y P (s - t) y = comp Y P s y - comp Y P t y := map_sub _ _ _

/-- Taking components kills the zero cochain. -/
@[simp]
theorem comp_zero {q : ℕ} (y : Fin (q + 1) → κ) : comp Y P (0 : Cochain Y P q) y = 0 :=
  map_zero _

/-- The Čech differential. -/
def dd {q : ℕ} (s : Cochain Y P q) : Cochain Y P (q + 1) :=
  ConcreteCategory.hom (((cechComplexFunctor Y).obj P).d q (q + 1)) s

/-- **The Čech differential, componentwise.** It is the alternating sum of the restrictions of
the components along the face maps of the tuple. -/
theorem comp_dd {q : ℕ} (s : Cochain Y P q) (x : Fin (q + 2) → κ) :
    comp Y P (dd Y P s) x = ∑ a : Fin (q + 2), (-1 : ℤ) ^ (a : ℕ) •
      res P (inter_le_inter Y x a.succAbove) (comp Y P s (x ∘ a.succAbove)) := by
  rw [dd, comp, ← ConcreteCategory.comp_apply, d_comp_π, hom_sum_apply]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- The Čech differential is additive. -/
@[simp]
theorem dd_add {q : ℕ} (s t : Cochain Y P q) : dd Y P (s + t) = dd Y P s + dd Y P t :=
  map_add _ _ _

/-- The Čech differential commutes with subtraction. -/
@[simp]
theorem dd_sub {q : ℕ} (s t : Cochain Y P q) : dd Y P (s - t) = dd Y P s - dd Y P t :=
  map_sub _ _ _

/-- The Čech differential kills the zero cochain. -/
@[simp]
theorem dd_zero {q : ℕ} : dd Y P (0 : Cochain Y P q) = 0 := map_zero _

/-- The Čech differential squares to zero. -/
theorem dd_dd {q : ℕ} (s : Cochain Y P q) : dd Y P (dd Y P s) = 0 := by
  rw [dd, dd, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
  rfl

/-- `CechSurj Y P q` says that every Čech cocycle of degree `q + 1` is a Čech coboundary; it is
the element form of the vanishing of the degree-`q + 1` Čech cohomology, see
`cechSurj_iff_isZero_homology`. -/
def CechSurj (q : ℕ) : Prop :=
  ∀ s : Cochain Y P (q + 1), dd Y P s = 0 → ∃ b : Cochain Y P q, dd Y P b = s

/-- **Čech vanishing in element form.** The degree-`q + 1` Čech cohomology vanishes exactly when
every Čech cocycle of degree `q + 1` is a Čech coboundary. -/
theorem cechSurj_iff_isZero_homology (q : ℕ) :
    CechSurj Y P q ↔ IsZero (((cechComplexFunctor Y).obj P).homology (q + 1)) := by
  rw [isZero_homology_succ_iff]
  rfl

end Cochains

/-! ### Reindexing the family along `ULift`

Tag 09SZ is stated for a family whose index type lives in the universe of the coefficients.
The families of interest here are indexed by a type in the universe of the space, so they must
first be reindexed along `ULift`; this changes nothing, because the intersection selected by a
tuple of lifted indices is *literally* the intersection selected by the underlying tuple. -/

section ULiftFamily

variable {X : Type u} [TopologicalSpace X] {κ : Type u} (Y : κ → Opens X)
  (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max u w})

/-- The family `Y` reindexed by a universe-lifted copy of its index type. -/
def uliftFamily : ULift.{w} κ → Opens X := fun i => Y i.down

/-- Reindexing the family along `ULift` does not change its union. -/
theorem iSup_uliftFamily : ⨆ i, (uliftFamily Y : ULift.{w} κ → Opens X) i = ⨆ i, Y i :=
  le_antisymm (iSup_le fun i => le_iSup Y i.down)
    (iSup_le fun i => le_iSup (uliftFamily Y : ULift.{w} κ → Opens X) (ULift.up i))

/-- The intersection selected by a tuple is contained in the one selected by the tuple of
lifted indices; in fact the two are equal. -/
theorem inter_le_uliftFamily {m : ℕ} (y : Fin m → κ) :
    inter Y y ≤ inter (uliftFamily Y : ULift.{w} κ → Opens X) fun a => ULift.up (y a) :=
  leOfHom (interLift (uliftFamily Y : ULift.{w} κ → Opens X) fun a => interπ Y y a)

/-- The intersection selected by a tuple of lifted indices is contained in the one selected by
the underlying tuple; in fact the two are equal. -/
theorem uliftFamily_inter_le {m : ℕ} (x : Fin m → ULift.{w} κ) :
    inter (uliftFamily Y : ULift.{w} κ → Opens X) x ≤ inter Y fun a => (x a).down :=
  leOfHom (interLift Y fun a => interπ (uliftFamily Y : ULift.{w} κ → Opens X) x a)

/-- The components of a Čech cochain, read as components of a cochain for the reindexed
family. -/
def cochainDownComp {q : ℕ} (s : Cochain Y P q) (x : Fin (q + 1) → ULift.{w} κ) :
    ToType (P.obj (op (inter (uliftFamily Y : ULift.{w} κ → Opens X) x))) :=
  res P (uliftFamily_inter_le Y x) (comp Y P s fun a => (x a).down)

/-- The components of a Čech cochain for the reindexed family, read as components of a cochain
for the family. -/
def cochainUpComp {q : ℕ} (s : Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q)
    (y : Fin (q + 1) → κ) : ToType (P.obj (op (inter Y y))) :=
  res P (inter_le_uliftFamily Y y)
    (comp (uliftFamily Y : ULift.{w} κ → Opens X) P s fun a => ULift.up (y a))

/-- A Čech cochain for the family, read as a Čech cochain for the reindexed family. -/
def cochainDown {q : ℕ} (s : Cochain Y P q) :
    Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q :=
  mk (uliftFamily Y : ULift.{w} κ → Opens X) P (cochainDownComp Y P s)

/-- A Čech cochain for the reindexed family, read as a Čech cochain for the family. -/
def cochainUp {q : ℕ} (s : Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q) :
    Cochain Y P q :=
  mk Y P (cochainUpComp Y P s)

/-- The components of the reindexed cochain. -/
@[simp]
theorem comp_cochainDown {q : ℕ} (s : Cochain Y P q) (x : Fin (q + 1) → ULift.{w} κ) :
    comp (uliftFamily Y : ULift.{w} κ → Opens X) P (cochainDown Y P s) x
      = res P (uliftFamily_inter_le Y x) (comp Y P s fun a => (x a).down) :=
  comp_mk (uliftFamily Y : ULift.{w} κ → Opens X) P (cochainDownComp Y P s) x

/-- The components of the cochain reindexed back. -/
@[simp]
theorem comp_cochainUp {q : ℕ} (s : Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q)
    (y : Fin (q + 1) → κ) :
    comp Y P (cochainUp Y P s) y = res P (inter_le_uliftFamily Y y)
      (comp (uliftFamily Y : ULift.{w} κ → Opens X) P s fun a => ULift.up (y a)) :=
  comp_mk Y P (cochainUpComp Y P s) y

/-- Reindexing kills the zero cochain. -/
theorem cochainDown_zero {q : ℕ} : cochainDown Y P (0 : Cochain Y P q) = 0 := by
  refine cochain_ext (uliftFamily Y : ULift.{w} κ → Opens X) P _ _ fun x => ?_
  rw [comp_cochainDown, comp_zero, comp_zero, res_zero]

/-- Reindexing commutes with the Čech differential. -/
theorem dd_cochainDown {q : ℕ} (s : Cochain Y P q) :
    dd (uliftFamily Y : ULift.{w} κ → Opens X) P (cochainDown Y P s)
      = cochainDown Y P (dd Y P s) := by
  refine cochain_ext (uliftFamily Y : ULift.{w} κ → Opens X) P _ _ fun x => ?_
  rw [comp_dd, comp_cochainDown, comp_dd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [comp_cochainDown, res_res, res_zsmul, res_res]
  exact congrArg _ (res_comp_congr Y P s rfl _ _)

/-- Reindexing back commutes with the Čech differential. -/
theorem dd_cochainUp {q : ℕ} (s : Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q) :
    dd Y P (cochainUp Y P s)
      = cochainUp Y P (dd (uliftFamily Y : ULift.{w} κ → Opens X) P s) := by
  refine cochain_ext Y P _ _ fun y => ?_
  rw [comp_dd, comp_cochainUp, comp_dd, res_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [comp_cochainUp, res_res, res_zsmul, res_res]
  exact congrArg _ (res_comp_congr (uliftFamily Y : ULift.{w} κ → Opens X) P s rfl _ _)

/-- Reindexing and reindexing back is the identity. -/
theorem cochainUp_cochainDown {q : ℕ} (s : Cochain Y P q) :
    cochainUp Y P (cochainDown Y P s : Cochain (uliftFamily Y : ULift.{w} κ → Opens X) P q)
      = s := by
  refine cochain_ext Y P _ _ fun y => ?_
  rw [comp_cochainUp, comp_cochainDown, res_res,
    res_comp_congr Y P s rfl _ (le_refl (inter Y y)), res_id]

/-- **Čech vanishing is insensitive to reindexing along `ULift`.** -/
theorem cechSurj_of_uliftFamily (q : ℕ)
    (h : CechSurj (uliftFamily Y : ULift.{w} κ → Opens X) P q) : CechSurj Y P q := by
  intro s hs
  obtain ⟨b, hb⟩ := h (cochainDown Y P s) (by rw [dd_cochainDown, hs, cochainDown_zero])
  exact ⟨cochainUp Y P b, by rw [dd_cochainUp, hb, cochainUp_cochainDown]⟩

end ULiftFamily

/-! ### Čech acyclicity of the injective objects

Beyond the exactness of the coefficient functor `T` (see `StacksDraft.Ch20.Sec11.Tag01EW`) the
proof of Tag 01EW uses exactly one property of the coefficients: the abelian sheaf underlying an
injective coefficient object has vanishing positive-degree Čech cohomology, for every family of
open subsets.  For sheaves of modules that is Stacks 01EA followed by Stacks 09SZ, proved here;
for abelian sheaves it is
`Stacks.Cohomology.AbelianVanishing.isZero_cechComplex_homology_of_injective`. -/

section Flasque

variable {X : Type u} [TopologicalSpace X]

/-- `CechAcyclicInjectives T` says that the abelian sheaf underlying an injective coefficient
object has vanishing positive-degree Čech cohomology — in the element form `CechSurj` — for
every family of open subsets indexed by a type in the universe of the space. -/
def CechAcyclicInjectives {𝒜 : Type u₂} [Category.{v₂} 𝒜]
    (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}) : Prop :=
  ∀ A : 𝒜, Injective A → ∀ {κ : Type u} (Y : κ → Opens X) (q : ℕ),
    CechSurj Y (abPresheaf T A) q

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})

/-- The sheaf of abelian groups underlying a sheaf of modules, read as a sheaf on the bundled
topological space, which is the form Tag 09SZ is stated for. -/
def topSheaf (A : SheafOfModules.{max u w} R) :
    TopCat.Sheaf AddCommGrpCat.{max u w} (TopCat.of X) :=
  (SheafOfModules.toSheaf R).obj A

/-- **An injective sheaf of modules is flasque**, by Stacks 01EA. -/
@[ega "0 12.2.1" "partial", sga "4 V 4.6" "special case"]
instance isFlasque_topSheaf (A : SheafOfModules.{max u w} R) [Injective A] :
    (topSheaf R A).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
      R A (leOfHom i.unop) y
    exact ⟨x, hx⟩

/-- **The positive-degree Čech cohomology of an injective sheaf of modules vanishes**, for every
family of open subsets. -/
theorem cechSurj_of_injective {κ : Type u} (Y : κ → Opens X) (A : SheafOfModules.{max u w} R)
    [Injective A] (q : ℕ) : CechSurj Y (abPresheaf (SheafOfModules.toSheaf R) A) q := by
  refine cechSurj_of_uliftFamily Y (abPresheaf (SheafOfModules.toSheaf R) A) q ?_
  rw [cechSurj_iff_isZero_homology]
  exact Stacks.Cohomology.FlasqueCech.isZero_cechComplex_homology_of_isFlasque
    (topSheaf R A) (⨆ i, (uliftFamily Y : ULift.{w} κ → Opens X) i)
    (uliftFamily Y : ULift.{w} κ → Opens X) rfl (q + 1) (Nat.succ_pos q)

/-- **Sheaves of modules are admissible coefficients for Tag 01EW**: the sheaf of abelian groups
underlying an injective sheaf of modules is Čech-acyclic in positive degrees. -/
theorem cechAcyclicInjectives_toSheaf :
    CechAcyclicInjectives (SheafOfModules.toSheaf.{max u w} R) := fun A hA _ Y q =>
  have := hA
  cechSurj_of_injective R Y A q

end Flasque

/-! ### Čech cochains with values in the coefficients -/

section SecCochain

variable {X : Type u} [TopologicalSpace X] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})

/-- The map on sections induced by a morphism of coefficients is additive, so it commutes
with finite sums. -/
theorem sec_sum {A A' : 𝒜} (g : A ⟶ A') (W : Opens X) {ι : Type*}
    (G : Finset ι) (f : ι → ToType ((abPresheaf T A).obj (op W))) :
    sec T g W (∑ i ∈ G, f i) = ∑ i ∈ G, sec T g W (f i) := map_sum _ _ _

variable {κ : Type u} (Y : κ → Opens X) {A A' : 𝒜} (g : A ⟶ A')

/-- The Čech cochain obtained by applying a morphism of coefficients to each component. -/
def secCochain {q : ℕ} (s : Cochain Y (abPresheaf T A) q) : Cochain Y (abPresheaf T A') q :=
  mk Y (abPresheaf T A') fun y => sec T g (inter Y y) (comp Y (abPresheaf T A) s y)

/-- The components of `secCochain`. -/
@[simp]
theorem comp_secCochain {q : ℕ} (s : Cochain Y (abPresheaf T A) q) (y : Fin (q + 1) → κ) :
    comp Y (abPresheaf T A') (secCochain T Y g s) y
      = sec T g (inter Y y) (comp Y (abPresheaf T A) s y) :=
  comp_mk Y (abPresheaf T A') _ y

/-- Applying a morphism of coefficients commutes with the Čech differential. -/
theorem dd_secCochain {q : ℕ} (s : Cochain Y (abPresheaf T A) q) :
    dd Y (abPresheaf T A') (secCochain T Y g s)
      = secCochain T Y g (dd Y (abPresheaf T A) s) := by
  refine cochain_ext Y (abPresheaf T A') _ _ fun x => ?_
  rw [comp_dd, comp_secCochain, comp_dd, sec_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [comp_secCochain, res_sec, sec_zsmul]

/-- Applying a morphism of coefficients kills the zero cochain. -/
@[simp]
theorem secCochain_zero {q : ℕ} : secCochain T Y g (0 : Cochain Y (abPresheaf T A) q) = 0 := by
  refine cochain_ext Y (abPresheaf T A') _ _ fun y => ?_
  rw [comp_secCochain, comp_zero, comp_zero, sec_zero]

/-- A cochain all of whose components are killed by a morphism of coefficients is killed
by it. -/
theorem secCochain_eq_zero {q : ℕ} (s : Cochain Y (abPresheaf T A) q)
    (hs : ∀ y, sec T g (inter Y y) (comp Y (abPresheaf T A) s y) = 0) :
    secCochain T Y g s = 0 := by
  refine cochain_ext Y (abPresheaf T A') _ _ fun y => ?_
  rw [comp_secCochain, comp_zero, hs]

/-- Applying a morphism of coefficients commutes with subtraction. -/
theorem secCochain_sub {q : ℕ} (s t : Cochain Y (abPresheaf T A) q) :
    secCochain T Y g (s - t) = secCochain T Y g s - secCochain T Y g t := by
  refine cochain_ext Y (abPresheaf T A') _ _ fun y => ?_
  rw [comp_secCochain, comp_sub, comp_sub, comp_secCochain, comp_secCochain, sec_sub]

end SecCochain

/-! ### The staircase

The classical dimension-shifting argument for Tag 01EW.  Fix an injective resolution `I` of `F`
and write `Zᵐ = ker(Iᵐ → Iᵐ⁺¹)` for its objects of cocycles.  A Čech cochain with values in
`Zᵐ` is handled as a Čech cochain with values in `Iᵐ` all of whose components are killed by the
differential; `CechSurjKer` is the vanishing statement in that form.  The step from `Zᵐ` to
`Zᵐ⁺¹` lifts a cocycle with values in `Zᵐ⁺¹` through `Iᵐ`, which is possible over the
intersections occurring in the Čech complex because `Hᵐ⁺¹` vanishes there, corrects the lift by
a cochain with values in `Zᵐ`, and descends using the Čech acyclicity of `Iᵐ`. -/

section Staircase

variable {X : Type u} [TopologicalSpace X] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})
  {κ : Type u} (Y : κ → Opens X)

/-- `CechSurjKer T Y dA q` says that every Čech cocycle of degree `q + 1` whose components are
killed by `dA` is the Čech coboundary of a cochain whose components are killed by `dA`; for `dA`
the `m`-th differential of an injective resolution this is the vanishing of the degree-`q + 1`
Čech cohomology of the object of `m`-cocycles. -/
def CechSurjKer {A A' : 𝒜} (dA : A ⟶ A') (q : ℕ) : Prop :=
  ∀ s : Cochain Y (abPresheaf T A) (q + 1),
    (∀ y, sec T dA (inter Y y) (comp Y (abPresheaf T A) s y) = 0) →
      dd Y (abPresheaf T A) s = 0 →
        ∃ b : Cochain Y (abPresheaf T A) q,
          (∀ y, sec T dA (inter Y y) (comp Y (abPresheaf T A) b y) = 0) ∧
            dd Y (abPresheaf T A) b = s

variable [Abelian 𝒜] [T.Additive] [PreservesFiniteLimits T]

variable {G A A' : 𝒜} (ιG : G ⟶ A) {dA : A ⟶ A'}
  (hzero : ιG ≫ dA = 0) (hker : IsLimit (KernelFork.ofι ιG hzero))

omit [PreservesFiniteLimits T] in
include hzero in
/-- The components of a cochain pushed forward along the inclusion of a kernel are killed by the
morphism whose kernel it is. -/
theorem sec_comp_secCochain_eq_zero {q : ℕ} (s : Cochain Y (abPresheaf T G) q)
    (y : Fin (q + 1) → κ) :
    sec T dA (inter Y y) (comp Y (abPresheaf T A) (secCochain T Y ιG s) y) = 0 := by
  rw [comp_secCochain, sec_sec, hzero, sec_of_zero]

include hzero hker in
/-- A cochain with values in a kernel is determined by its image. -/
theorem secCochain_injective {q : ℕ} (s t : Cochain Y (abPresheaf T G) q)
    (h : secCochain T Y ιG s = secCochain T Y ιG t) : s = t := by
  refine cochain_ext Y (abPresheaf T G) _ _ fun y => ?_
  refine injective_sec_of_isLimit T ιG hzero hker (inter Y y) ?_
  rw [← comp_secCochain T Y ιG s y, ← comp_secCochain T Y ιG t y, h]

include hzero hker in
/-- A cochain whose components are killed by `dA` comes from a cochain with values in the
kernel. -/
theorem exists_secCochain_eq {q : ℕ} (s : Cochain Y (abPresheaf T A) q)
    (hs : ∀ y, sec T dA (inter Y y) (comp Y (abPresheaf T A) s y) = 0) :
    ∃ c : Cochain Y (abPresheaf T G) q, secCochain T Y ιG c = s := by
  choose c hc using fun y : Fin (q + 1) → κ =>
    exists_sec_eq_of_isLimit T ιG hzero hker (inter Y y) _ (hs y)
  refine ⟨mk Y (abPresheaf T G) c, cochain_ext Y (abPresheaf T A) _ _ fun y => ?_⟩
  rw [comp_secCochain, comp_mk, hc]

include ιG hzero hker in
/-- **Čech vanishing for a kernel, read off the ambient coefficients.** -/
theorem cechSurjKer_of_cechSurj (q : ℕ) (h : CechSurj Y (abPresheaf T G) q) :
    CechSurjKer T Y dA q := by
  intro s hs hdd
  obtain ⟨c, hc⟩ := exists_secCochain_eq T Y ιG hzero hker s hs
  have hcdd : dd Y (abPresheaf T G) c = 0 := by
    refine secCochain_injective T Y ιG hzero hker _ _ ?_
    rw [← dd_secCochain, hc, hdd, secCochain_zero]
  obtain ⟨b, hb⟩ := h c hcdd
  refine ⟨secCochain T Y ιG b, sec_comp_secCochain_eq_zero T Y ιG hzero b, ?_⟩
  rw [dd_secCochain, hb, hc]

include ιG hzero hker in
/-- **Čech vanishing for a kernel, in the form `CechSurj`.** -/
theorem cechSurj_of_cechSurjKer (q : ℕ) (h : CechSurjKer T Y dA q) :
    CechSurj Y (abPresheaf T G) q := by
  intro s hs
  obtain ⟨b, hbker, hb⟩ := h (secCochain T Y ιG s) (sec_comp_secCochain_eq_zero T Y ιG hzero s)
    (by rw [dd_secCochain, hs, secCochain_zero])
  obtain ⟨c, hc⟩ := exists_secCochain_eq T Y ιG hzero hker b hbker
  refine ⟨c, secCochain_injective T Y ιG hzero hker _ _ ?_⟩
  rw [← dd_secCochain, hc, hb]

variable [PreservesFiniteColimits T]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}]
  [EnoughInjectives 𝒜]

omit [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}] in
/-- **Lifting through the resolution.** If `Hᵐ⁺¹(V, F)` vanishes, then a section of `Iᵐ⁺¹` over
`V` killed by the next differential is the image under the differential of a section of `Iᵐ`:
the complex of sections of the resolution over `V` computes `H⁎(V, F)`, so it is exact in
degree `m + 1`. -/
theorem exists_sec_eq_d_of_isZero {F : 𝒜} (I : InjectiveResolution F)
    (V : Opens X) (m : ℕ) (hV : IsZero (Hobj T V (m + 1) F))
    (z : ToType ((abPresheaf T (I.cocomplex.X (m + 1))).obj (op V)))
    (hz : sec T (I.cocomplex.d (m + 1) (m + 2)) V z = 0) :
    ∃ y : ToType ((abPresheaf T (I.cocomplex.X m)).obj (op V)),
      sec T (I.cocomplex.d m (m + 1)) V y = z := by
  have hex : IsZero ((secComplex T I V).homology (m + 1)) :=
    IsZero.of_iso hV (I.isoRightDerivedObj (secFunctor T V) (m + 1)).symm
  exact (isZero_homology_succ_iff m).1 hex z hz

omit [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}] in
/-- **The staircase step.** Assume that `Hᵐ⁺¹(V, F)` vanishes over every intersection `V` of
members of the family, and that every Čech cocycle of degree `q + 2` with values in the object of
`m`-cocycles of `I` is a coboundary there.  Then every Čech cocycle of degree `q + 1` with values
in the `m + 1`-cocycles is a coboundary: lift it componentwise through `Iᵐ`, correct the
lift by a cochain with values in the `m`-cocycles so that it becomes a Čech cocycle, and write
that cocycle as a coboundary using the Čech acyclicity of the injective object `Iᵐ`. -/
theorem cechSurjKer_succ (hacyc : CechAcyclicInjectives T) {F : 𝒜}
    (I : InjectiveResolution F) (m q : ℕ)
    (hH : ∀ (k : ℕ) (y : Fin (k + 1) → κ), IsZero (Hobj T (inter Y y) (m + 1) F))
    (ih : CechSurjKer T Y (I.cocomplex.d m (m + 1)) (q + 1)) :
    CechSurjKer T Y (I.cocomplex.d (m + 1) (m + 2)) q := by
  intro c hcker hcdd
  choose b hb using fun x : Fin (q + 2) → κ =>
    exists_sec_eq_d_of_isZero T I (inter Y x) m (hH _ x)
      (comp Y (abPresheaf T (I.cocomplex.X (m + 1))) c x) (hcker x)
  have hBc : secCochain T Y (I.cocomplex.d m (m + 1))
      (mk Y (abPresheaf T (I.cocomplex.X m)) b) = c := by
    refine cochain_ext Y (abPresheaf T (I.cocomplex.X (m + 1))) _ _ fun x => ?_
    rw [comp_secCochain, comp_mk, hb]
  set B := mk Y (abPresheaf T (I.cocomplex.X m)) b
  have hEker : ∀ y, sec T (I.cocomplex.d m (m + 1)) (inter Y y)
      (comp Y (abPresheaf T (I.cocomplex.X m)) (dd Y (abPresheaf T (I.cocomplex.X m)) B) y)
      = 0 := by
    intro y
    have hz : comp Y (abPresheaf T (I.cocomplex.X (m + 1)))
        (secCochain T Y (I.cocomplex.d m (m + 1))
          (dd Y (abPresheaf T (I.cocomplex.X m)) B)) y = 0 := by
      rw [← dd_secCochain, hBc, hcdd, comp_zero]
    rw [comp_secCochain] at hz
    exact hz
  obtain ⟨h, hhker, hh⟩ := ih _ hEker (dd_dd Y (abPresheaf T (I.cocomplex.X m)) B)
  obtain ⟨a, ha⟩ := hacyc (I.cocomplex.X m) (I.injective m) Y q (B - h) (by
    rw [dd_sub, hh, sub_self])
  refine ⟨secCochain T Y (I.cocomplex.d m (m + 1)) a, fun y => ?_, ?_⟩
  · rw [comp_secCochain, sec_sec, I.cocomplex.d_comp_d, sec_of_zero]
  · rw [dd_secCochain, ha, secCochain_sub, hBc,
      secCochain_eq_zero T Y (I.cocomplex.d m (m + 1)) h hhker, sub_zero]

omit [PreservesFiniteColimits T]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}] in
/-- **The staircase.** Let `n` be a degree such that `Hʲ(V, F)` vanishes for `0 < j ≤ n` over
every intersection of members of the family, and assume the positive-degree Čech cohomology of
`F` vanishes for the family.  Then, for every `m ≤ n`, every Čech cocycle with values in the
object of `m`-cocycles of `I` is a coboundary.  The recursion on `m` starts at `m = 0`, where the
object of `0`-cocycles is `F` itself. -/
theorem cechSurjKer_of_le (hacyc : CechAcyclicInjectives T) {F : 𝒜}
    (I : InjectiveResolution F) (n : ℕ)
    (hCech : ∀ q, CechSurj Y (abPresheaf T F) q)
    (hH : ∀ j, 0 < j → j ≤ n → ∀ (k : ℕ) (y : Fin (k + 1) → κ),
      IsZero (Hobj T (inter Y y) j F))
    (m : ℕ) (hm : m ≤ n) : ∀ q, CechSurjKer T Y (I.cocomplex.d m (m + 1)) q := by
  induction m with
  | zero =>
    intro q
    exact cechSurjKer_of_cechSurj T Y (resolutionι I) (resolutionι_comp_d I)
      (isLimitKernelForkι I) q (hCech q)
  | succ m ihm =>
    intro q
    exact cechSurjKer_succ T Y hacyc I m q (hH (m + 1) (Nat.succ_pos m) hm)
      (ihm (Nat.le_of_succ_le hm) (q + 1))

end Staircase

/-! ### Stacks Tag 01EW -/

section Main

variable {X : Type u} [TopologicalSpace X] {𝒜 : Type u₂} [Category.{v₂} 𝒜] [Abelian 𝒜]
  (T : 𝒜 ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}]
  [EnoughInjectives 𝒜]

/-- **Tag 01EW up to a given degree.** Under the hypotheses of Tag 01EW, the cohomology
`Hʲ(V, F)` vanishes over every member `V` of the basis, for every `j` with `0 < j ≤ n`.

The proof is by induction on `n`.  At the inductive step the degree `n + 1` is reduced, by
`Stacks.Cohomology.Basis.isZero_Hobj_succ_of_cech_isZero`, to the degree-one Čech vanishing
for the object of `n`-cocycles of an injective resolution, which the staircase
`cechSurjKer_of_le` provides from the inductive hypothesis: the latter applies because the
intersections occurring in the Čech complex of a cover in `Cov` belong to `B`, which is what
`hCovBasis` asks. -/
theorem isZero_Hobj_of_le (hacyc : CechAcyclicInjectives T) (F : 𝒜) (B : Set (Opens X))
    (Cov : Set (OpenCover X))
    (hCovBasis : ∀ U ∈ Cov, U.carrier ∈ B ∧ (∀ i, U.obj i ∈ B) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → U.ι), (⨅ k, U.obj (s k)) ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ V : OpenCover X, V.carrier = U →
      ∃ W ∈ Cov, W.carrier = U ∧ W.Refines V)
    (hCech : ∀ U ∈ Cov, ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor U.obj).obj (abPresheaf T F)).homology n))
    (I : InjectiveResolution F) (n : ℕ) :
    ∀ V ∈ B, ∀ j, 0 < j → j ≤ n → IsZero (Hobj T V j F) := by
  induction n with
  | zero => exact fun V _ j hj hjn => absurd (hj.trans_le hjn) (lt_irrefl 0)
  | succ n ihn =>
    intro V hV j hj hjn
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact ihn V hV j hj (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : j = n + 1 := le_antisymm hjn hge
      have hcyc : ∀ W ∈ Cov, IsZero (((cechComplexFunctor W.obj).obj
          (abPresheaf T (I.cocomplex.cycles n))).homology 1) := by
        intro W hW
        refine (cechSurj_iff_isZero_homology W.obj
          (abPresheaf T (I.cocomplex.cycles n)) 0).1 ?_
        refine cechSurj_of_cechSurjKer T W.obj (I.cocomplex.iCycles n)
          (I.cocomplex.iCycles_d n (n + 1))
          (I.cocomplex.cyclesIsKernel n (n + 1) (by simp)) 0 ?_
        refine cechSurjKer_of_le T W.obj hacyc I n (fun q => ?_) (fun j hj hjn k y => ?_)
          n le_rfl 0
        · exact (cechSurj_iff_isZero_homology W.obj (abPresheaf T F) q).2
            (hCech W hW (q + 1) (Nat.succ_pos q))
        · refine ihn (inter W.obj y) ?_ j hj hjn
          rw [inter_eq_iInf]
          exact (hCovBasis W hW).2.2 k y
      exact isZero_Hobj_succ_of_cech_isZero T I n (I.cocomplex.iCycles n)
        (I.cocomplex.iCycles_d n (n + 1)) (I.cocomplex.cyclesIsKernel n (n + 1) (by simp))
        B Cov hCovCofinal hcyc V hV

/-- **Stacks Tag 01EW, for an arbitrary category of coefficients.** Let `B` be a basis of open
subsets of `X` and let `Cov` be a collection of open covers by members of `B` whose finite
intersections also lie in `B`.  If every open cover of a member of `B` is refined by a member of
`Cov` covering it, and the positive-degree Čech cohomology of `F` vanishes for every cover in
`Cov`, then the higher cohomology of `F` vanishes over every member of `B`.

The coefficients are any abelian category with enough injectives carrying an exact functor `T` to
the abelian sheaves on `X` whose injective objects become Čech-acyclic, `hacyc`.  Sheaves of
modules are the case `T = SheafOfModules.toSheaf R`, which is
`isZero_hgroup_of_cech_isZero_on_basis` below; abelian sheaves are the case `T = 𝟭`.

The hypothesis that `B` is a basis is not needed: the cofinality hypothesis `hCovCofinal` already
provides all the covers the proof uses.  It is kept because it is part of the statement of the
tag. -/
theorem isZero_Hobj_of_cech_isZero_on_basis (hacyc : CechAcyclicInjectives T) (F : 𝒜)
    (B : Set (Opens X)) (_hB : Opens.IsBasis B) (Cov : Set (OpenCover X))
    (hCovBasis : ∀ U ∈ Cov, U.carrier ∈ B ∧ (∀ i, U.obj i ∈ B) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → U.ι), (⨅ k, U.obj (s k)) ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ V : OpenCover X, V.carrier = U →
      ∃ W ∈ Cov, W.carrier = U ∧ W.Refines V)
    (hCech : ∀ U ∈ Cov, ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor U.obj).obj (abPresheaf T F)).homology n))
    (U : Opens X) (hU : U ∈ B) (n : ℕ) (hn : 0 < n) :
    IsZero (Hobj T U n F) :=
  isZero_Hobj_of_le T hacyc F B Cov hCovBasis hCovCofinal hCech
    (InjectiveResolution.of F) n U hU n hn le_rfl

end Main

/-! ### Stacks Tag 01EW for sheaves of modules -/

section Modules

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u w}]
  [EnoughInjectives (SheafOfModules.{max u w} R)]

/-- **Stacks Tag 01EW.** Let `B` be a basis of open subsets of a ringed space and let `Cov` be a
collection of open covers by members of `B` whose finite intersections also lie in `B`.  If every
open cover of a member of `B` is refined by a member of `Cov` covering it, and the positive-degree
Čech cohomology of `F` vanishes for every cover in `Cov`, then the higher cohomology of `F`
vanishes over every member of `B`.

This is the case `T = SheafOfModules.toSheaf R` of `isZero_Hobj_of_cech_isZero_on_basis`: the
Čech acyclicity of the injective objects is `cechAcyclicInjectives_toSheaf`, Stacks 01EA followed
by Stacks 09SZ.

The hypothesis that `B` is a basis is not needed: the cofinality hypothesis `hCovCofinal` already
provides all the covers the proof uses.  It is kept because it is part of the statement of the
tag. -/
@[stacks 01EW]
theorem isZero_hgroup_of_cech_isZero_on_basis (F : SheafOfModules.{max u w} R)
    (B : Set (Opens X)) (_hB : Opens.IsBasis B) (Cov : Set (OpenCover X))
    (hCovBasis : ∀ U ∈ Cov, U.carrier ∈ B ∧ (∀ i, U.obj i ∈ B) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → U.ι), (⨅ k, U.obj (s k)) ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ V : OpenCover X, V.carrier = U →
      ∃ W ∈ Cov, W.carrier = U ∧ W.Refines V)
    (hCech : ∀ U ∈ Cov, ∀ n : ℕ, 0 < n → CechCohomologyIsZero R F U n)
    (U : Opens X) (hU : U ∈ B) (n : ℕ) (hn : 0 < n) :
    IsZero (Hgroup R U n F) :=
  isZero_Hobj_of_cech_isZero_on_basis (SheafOfModules.toSheaf R)
    (cechAcyclicInjectives_toSheaf R) F B _hB Cov hCovBasis hCovCofinal hCech U hU n hn

end Modules

end

end Stacks.Cohomology.BasisCycles

end
