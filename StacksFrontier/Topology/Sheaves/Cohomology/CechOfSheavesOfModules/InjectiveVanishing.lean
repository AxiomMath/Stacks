module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasisDegreeOne
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.ModuleValuedComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing

/-!
# Čech cohomology of an injective sheaf of modules, in positive degrees

The positive-degree module-valued Čech cohomology of an injective sheaf of modules vanishes.

## Main definitions

* `mcomp` takes the components of a cochain of the module-valued Čech complex, `mmk` builds a
  cochain from prescribed components and `md` is the differential on elements.

## Main results

* `isZero_cechComplex_homology_of_injective` is the positive-degree half of Stacks Tag 01EP.

## Implementation notes

The mathematical input is the Čech acyclicity of flasque abelian sheaves, Stacks Tag 09SZ,
through the element form `Stacks.Cohomology.FlasqueCech.vanishing` of its relative Čech
complexes. Flasqueness of the abelian sheaf underlying an injective sheaf of modules is
`underlying_isFlasque`.

Everything is done on *elements*, so that no isomorphism of cochain complexes has to be
built. Three transports are needed, and each of them is invisible on components:

* from the module-valued complex to the abelian-group-valued one: a component of a cochain of
  `cechComplex V U hU I` over the slice category `Over V` is, definitionally, a section of `I`,
  and the differential acts on it by restriction along an inclusion of opens; this is checked
  by `rfl` in `mcomp_md`;
* from the slice category to the opens of the space: the only thing needed is
  `inter_coverObject_left`, the identification of the open underlying a product in `Over V`
  with the corresponding intersection in `Opens X`;
* from the index type `ι` to a model of it in the universe of the coefficients, which is the
  universe Tag 09SZ ties the index type to; `Shrink` provides the model.

The degree-zero clause of the tag is not proved here, so no declaration in this file carries
that clause. Its statement is about the canonical map from sections on the covered open to
degree-zero Čech cohomology, and stating it needs the comparison `sectionsToSlice` between
sections over `V` and sections at the terminal object of the slice over `V`; the two carry the
same underlying group with module structures that differ by restriction of scalars along
`R(V) ⟶ R(V)`, a map that is the identity but not syntactically so, which is why instance
synthesis fails on the scalar action. The repair is to build that comparison as
`ModuleCat.restrictScalarsId'App`, whose whole purpose is a restriction of scalars along a map
only provably equal to the identity.

The two further things this paragraph used to list as missing are no longer: the sheaf
condition for the module-valued complex over the slice, as a kernel of the first differential,
is `CechSheaf.isIso_kernelLift_cechAugmentation`, and the identification of degree-zero
homology with that kernel is `CechSheaf.homologyZeroIso`, both in
`StacksDraft.Ch20.Sec17.Tag01EPZero`. The change of scalars above is the only remaining step.

All three transports are absorbed by `Stacks.Cohomology.Basis.res`, which takes a section along an
inclusion of opens given as a *proof*: equalities of opens therefore need no `eqToHom`, and
`res_res` composes them away. This is the device that makes the element layer of
`StacksDraft.Ch20.Sec17.Tag09SZ` usable here.

The element layer for the module-valued complex is built from `Stacks.CategoryTheory.CechComplex`,
whose `π`, `lift` and `d_comp_π` mention only the terms `X n` of the complex and never the
cosimplicial powers `_ ^⦋n⦌`; this is why no `set_option` is needed. Components of a cochain
are extracted with `Concrete.isLimit_ext` and produced through the forgetful functor to abelian
groups, which preserves the products involved, so that the free abelian group on one generator
can serve as the source of the universal map.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sub res_sum res_zsmul
  ofElt ofElt_apply)


universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechSheaf

noncomputable section

/-- Applying a finite sum of maps of modules to an element. -/
theorem moduleCat_hom_sum_apply {S : Type*} [Ring S] {M N : ModuleCat.{uM} S} {κ : Type*}
    (G : Finset κ) (f : κ → (M ⟶ N)) (s : ToType M) :
    ConcreteCategory.hom (∑ i ∈ G, f i) s = ∑ i ∈ G, ConcreteCategory.hom (f i) s := by
  classical
  induction G using Finset.induction with
  | empty => simp
  | insert a G ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- Reindexing a tuple enlarges the intersection it selects. -/
theorem inter_le_reindex {Y : Type*} [TopologicalSpace Y] {κ : Type*} (W : κ → Opens Y)
    {m m' : ℕ} (x : Fin m → κ) (h : Fin m' → Fin m) : inter W x ≤ inter W (x ∘ h) :=
  leOfHom (interMap W x h)

/-- Restricting an alternating sum of restrictions restricts each of its terms. -/
private theorem res_alt_sum_res {Y : Type*} [TopologicalSpace Y]
    (Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{uM}) {N : ℕ} {A B : Opens Y} (hBA : B ≤ A)
    {C : Fin N → Opens Y} (h1 : ∀ a, A ≤ C a)
    (f : ∀ a, ToType (Q.obj (op (C a)))) :
    res Q hBA (∑ a : Fin N, (-1 : ℤ) ^ (a : ℕ) • res Q (h1 a) (f a)) =
      ∑ a : Fin N, (-1 : ℤ) ^ (a : ℕ) • res Q (hBA.trans (h1 a)) (f a) := by
  rw [res_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [res_zsmul, res_res]

/-! ### Tag 09SZ in component form -/

section Flasque

variable {T : TopCat.{uX}} {κ : Type uM} (W : κ → Opens T)
  (F : TopCat.Sheaf AddCommGrpCat.{uM} T)

/-- **Stacks 09SZ, in component form.** Let `F` be a flasque sheaf of abelian groups. A family
of sections of `F` over the intersections selected by the tuples of length `q + 2`, whose
alternating sum of restrictions along the face maps vanishes, is itself the alternating sum of
restrictions of a family indexed by the tuples of length `q + 1`. -/
theorem exists_sum_res_eq [F.IsFlasque] (q : ℕ)
    (g : ∀ y : Fin (q + 2) → κ, ToType (F.obj.obj (op (inter W y))))
    (hg : ∀ x : Fin (q + 3) → κ, ∑ a : Fin (q + 3), (-1 : ℤ) ^ (a : ℕ) •
      res F.obj (inter_le_reindex W x a.succAbove) (g (x ∘ a.succAbove)) = 0) :
    ∃ h : ∀ y : Fin (q + 1) → κ, ToType (F.obj.obj (op (inter W y))),
      ∀ x : Fin (q + 2) → κ, ∑ a : Fin (q + 2), (-1 : ℤ) ^ (a : ℕ) •
        res F.obj (inter_le_reindex W x a.succAbove) (h (x ∘ a.succAbove)) = g x := by
  have hzero : FlasqueCech.rd (FlasqueCech.rmk (fun y => res F.obj inf_le_left (g y)) :
      FlasqueCech.RelCochain W F.obj (q + 1) ⊤) = 0 := by
    refine FlasqueCech.rcochain_ext _ _ fun x => ?_
    rw [FlasqueCech.rcomp_zero, FlasqueCech.rcomp_rd]
    have hgx := res_alt_sum_res F.obj (inf_le_left : inter W x ⊓ ⊤ ≤ inter W x)
      (fun a => inter_le_reindex W x a.succAbove) fun a => g (x ∘ a.succAbove)
    rw [hg x, res_zero] at hgx
    simpa only [FlasqueCech.rcomp_rmk, res_res] using hgx.symm
  obtain ⟨b, hb⟩ := FlasqueCech.vanishing_isFlasque W F q ⊤ trivial _ hzero
  refine ⟨fun y => res F.obj (le_inf le_rfl le_top) (FlasqueCech.rcomp b y), fun x => ?_⟩
  have key : FlasqueCech.rcomp (FlasqueCech.rd b) x = res F.obj inf_le_left (g x) := by
    rw [hb, FlasqueCech.rcomp_rmk]
  rw [FlasqueCech.rcomp_rd] at key
  have key2 := (res_alt_sum_res F.obj (le_inf le_rfl le_top : inter W x ≤ inter W x ⊓ ⊤)
    (fun a => inf_le_inf_right ⊤ (inter_le_reindex W x a.succAbove))
    fun a => FlasqueCech.rcomp b (x ∘ a.succAbove)).symm.trans (congrArg _ key)
  simp only [res_res, res_id] at key2 ⊢
  exact key2

end Flasque

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]

/-! ### The presheaf of abelian groups of sections -/

/-- The presheaf of abelian groups of sections of a sheaf of modules. -/
abbrev abSections (I : SheafOfModules.{uM} R) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{uM} :=
  ((SheafOfModules.toSheaf R).obj I).obj

/-- The sheaf of abelian groups underlying a sheaf of modules, on the topological space. -/
abbrev abSheaf (I : SheafOfModules.{uM} R) :
    TopCat.Sheaf AddCommGrpCat.{uM} (TopCat.of X) :=
  ⟨abSections I, ((SheafOfModules.toSheaf R).obj I).property⟩

/-! ### The open underlying a product in the slice category -/

variable (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)

omit [UnivLE.{uI, uM}] in
/-- The members of the cover, viewed in the slice over `V`, have the expected underlying open. -/
theorem coverObject_left (i : ι) : (coverObject U hU i).left = U i := rfl

omit [UnivLE.{uI, uM}] in
include hU in
/-- A nonempty intersection of members of the cover is contained in the covered open. -/
theorem inter_le_covered {m : ℕ} (x : Fin (m + 1) → ι) : inter U x ≤ V :=
  (leOfHom (interπ U x 0)).trans (by rw [hU]; exact le_iSup U (x 0))

omit [UnivLE.{uI, uM}] in
/-- **The product in the slice category is the intersection.** The open underlying the product
in `Over V` of the members of the cover selected by a nonempty tuple is their intersection in
`Opens X`. -/
theorem inter_coverObject_left {m : ℕ} (x : Fin (m + 1) → ι) :
    (inter (coverObject U hU) x).left = inter U x := by
  refine le_antisymm ?_ ?_
  · rw [inter_eq_iInf U x]
    exact le_iInf fun a => leOfHom (interπ (coverObject U hU) x a).left
  · exact leOfHom (interLift (coverObject U hU)
      (T := Over.mk (homOfLE (inter_le_covered V U hU (m := m) x)))
      (fun a => Over.homMk (homOfLE (leOfHom (interπ U x a))))).left

/-! ### Elements of the module-valued Čech complex -/

section Elements

variable (I : SheafOfModules.{uM} R)

/-- The raw component of a cochain of the module-valued Čech complex at a tuple: a section of
`I` over the open underlying the corresponding product in the slice category. -/
def rawcomp {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    ToType ((abSections I).obj (op (inter (coverObject U hU) x).left)) :=
  ConcreteCategory.hom (π (coverObject U hU) (sectionsPresheaf V I) n x) s

/-- **The component of a cochain of the module-valued Čech complex at a tuple**: a section of
`I` over the intersection of the members of the cover selected by the tuple. -/
def mcomp {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    ToType ((abSections I).obj (op (inter U x))) :=
  res (abSections I) (inter_coverObject_left V U hU x).ge (rawcomp V U hU I s x)

/-- The raw component is recovered from the component by restriction along an equality. -/
theorem res_mcomp {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    res (abSections I) (inter_coverObject_left V U hU x).le (mcomp V U hU I s x) =
      rawcomp V U hU I s x := by
  rw [mcomp, res_res]
  exact res_id _ _

/-- The universal map out of the free abelian group on one generator attached to a family of
prescribed components. -/
def mlift {n : ℕ}
    (f : ∀ x : Fin (n + 1) → ι, ToType ((abSections I).obj (op (inter U x)))) :
    AddCommGrpCat.of (ULift.{uM} ℤ) ⟶
      (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).obj
        (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n) :=
  IsLimit.lift
    (isLimitOfPreserves (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM})
      (isLimitFan (coverObject U hU) (sectionsPresheaf V I) n))
    (Cone.mk (AddCommGrpCat.of (ULift.{uM} ℤ))
      (Discrete.natTrans fun x =>
        ofElt (res (abSections I) (inter_coverObject_left V U hU x.as).le (f x.as))))

/-- The universal map attached to prescribed components has those components. -/
theorem mlift_comp_π {n : ℕ}
    (f : ∀ x : Fin (n + 1) → ι, ToType ((abSections I).obj (op (inter U x))))
    (x : Fin (n + 1) → ι) :
    mlift V U hU I f ≫
        (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM}).map
          (π (coverObject U hU) (sectionsPresheaf V I) n x) =
      ofElt (res (abSections I) (inter_coverObject_left V U hU x).le (f x)) :=
  (isLimitOfPreserves (forget₂ (ModuleCat.{uM} (SectionRing R V)) AddCommGrpCat.{uM})
    (isLimitFan (coverObject U hU) (sectionsPresheaf V I) n)).fac _ ⟨x⟩

/-- The cochain of the module-valued Čech complex with prescribed components. -/
def mmk {n : ℕ}
    (f : ∀ x : Fin (n + 1) → ι, ToType ((abSections I).obj (op (inter U x)))) :
    ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n) :=
  ConcreteCategory.hom (mlift V U hU I f) (ULift.up 1)

/-- The raw components of `mmk` are the restrictions of the prescribed sections. -/
theorem rawcomp_mmk {n : ℕ}
    (f : ∀ x : Fin (n + 1) → ι, ToType ((abSections I).obj (op (inter U x))))
    (x : Fin (n + 1) → ι) :
    rawcomp V U hU I (mmk V U hU I f) x =
      res (abSections I) (inter_coverObject_left V U hU x).le (f x) := by
  have h := ConcreteCategory.congr_hom (mlift_comp_π V U hU I f x) (ULift.up (1 : ℤ))
  rw [ConcreteCategory.comp_apply] at h
  exact h.trans (ofElt_apply _)

/-- The components of `mmk` are the prescribed sections. -/
@[simp]
theorem mcomp_mmk {n : ℕ}
    (f : ∀ x : Fin (n + 1) → ι, ToType ((abSections I).obj (op (inter U x))))
    (x : Fin (n + 1) → ι) : mcomp V U hU I (mmk V U hU I f) x = f x := by
  rw [mcomp, rawcomp_mmk, res_res]
  exact res_id _ _

/-- A cochain of the module-valued Čech complex is determined by its components. -/
theorem mcech_ext {n : ℕ}
    (s t : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (h : ∀ x, mcomp V U hU I s x = mcomp V U hU I t x) : s = t := by
  refine Concrete.isLimit_ext _
    (isLimitFan (coverObject U hU) (sectionsPresheaf V I) n) s t ?_
  rintro ⟨x⟩
  have hx : rawcomp V U hU I s x = rawcomp V U hU I t x := by
    rw [← res_mcomp V U hU I s x, ← res_mcomp V U hU I t x, h x]
  exact hx

/-- Taking components kills the zero cochain. -/
@[simp]
theorem mcomp_zero {n : ℕ} (x : Fin (n + 1) → ι) :
    mcomp V U hU I
      (0 : ToType
        (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) x = 0 := by
  have h0 : rawcomp V U hU I
      (0 : ToType
        (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) x = 0 :=
    map_zero _
  rw [mcomp, h0, res_zero]

/-- The differential of the module-valued Čech complex, on elements. -/
def md {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n)) :
    ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X (n + 1)) :=
  ConcreteCategory.hom
    (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).d n (n + 1)) s

/-- The differential of the module-valued Čech complex, on raw components. -/
theorem rawcomp_md {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 2) → ι) :
    rawcomp V U hU I (md V U hU I s) x =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        res (abSections I)
          (leOfHom (interMap (coverObject U hU) x a.succAbove).left)
          (rawcomp V U hU I s (x ∘ a.succAbove)) := by
  rw [rawcomp, md, ← ConcreteCategory.comp_apply, d_comp_π, moduleCat_hom_sum_apply]
  exact Finset.sum_congr rfl fun a _ => rfl

/-- **The differential of the module-valued Čech complex, componentwise.** It is the
alternating sum of the restrictions of the components along the face maps of the tuple. -/
theorem mcomp_md {n : ℕ}
    (s : ToType
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 2) → ι) :
    mcomp V U hU I (md V U hU I s) x =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        res (abSections I) (inter_le_reindex U x a.succAbove)
          (mcomp V U hU I s (x ∘ a.succAbove)) := by
  rw [mcomp, rawcomp_md, res_alt_sum_res]
  simp only [mcomp, res_res]

/-- The componentwise cocycle identity: the alternating sum of the restricted components of a
cocycle of the module-valued Čech complex vanishes. -/
theorem sum_res_mcomp_eq_zero {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (hs : md V U hU I s = 0) (x : Fin (n + 2) → ι) {W : Opens X} (hW : W ≤ inter U x) :
    ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
      res (abSections I) (hW.trans (inter_le_reindex U x a.succAbove))
        (mcomp V U hU I s (x ∘ a.succAbove)) = 0 := by
  have h0 : mcomp V U hU I (md V U hU I s) x = 0 := by rw [hs, mcomp_zero]
  rw [mcomp_md] at h0
  rw [← res_alt_sum_res (abSections I) hW (fun a => inter_le_reindex U x a.succAbove), h0,
    res_zero]

/-- Components of a cochain at equal tuples, restricted to a common open, agree. -/
theorem res_mcomp_congr {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    {x x' : Fin (n + 1) → ι} (hx : x = x') {W : Opens X} (h : W ≤ inter U x)
    (h' : W ≤ inter U x') :
    res (abSections I) h (mcomp V U hU I s x) =
      res (abSections I) h' (mcomp V U hU I s x') := by
  subst hx
  rfl

/-- **Every positive-degree cocycle is a coboundary.** For an injective sheaf of modules, a
cocycle of the module-valued Čech complex in a positive degree is the differential of a
cochain one degree down. -/
theorem exists_md_eq [Injective I] {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X (n + 1)))
    (hs : md V U hU I s = 0) :
    ∃ b, md V U hU I b = s := by
  have : (abSheaf I).IsFlasque := underlying_isFlasque I
  obtain ⟨κ, τ, σ, hστ⟩ : ∃ (κ : Type uM) (τ : ι → κ) (σ : κ → ι), ∀ i, σ (τ i) = i :=
    ⟨Shrink.{uM} ι, equivShrink ι, (equivShrink ι).symm,
      fun i => (equivShrink ι).symm_apply_apply i⟩
  have hcomp : ∀ {m : ℕ} (y : Fin m → ι), σ ∘ (τ ∘ y) = y :=
    fun y => funext fun a => hστ (y a)
  have hint : ∀ {m : ℕ} (y : Fin m → ι), inter (fun k => U (σ k)) (τ ∘ y) = inter U y :=
    fun y => congrArg (inter U) (hcomp y)
  obtain ⟨g, hg⟩ := exists_sum_res_eq (T := TopCat.of X) (fun k => U (σ k)) (abSheaf I) n
    (fun y => mcomp V U hU I s (σ ∘ y))
    (fun y => sum_res_mcomp_eq_zero V U hU I s hs (σ ∘ y) le_rfl)
  refine ⟨mmk V U hU I (fun y => res (abSections I) (hint y).ge (g (τ ∘ y))), ?_⟩
  refine mcech_ext V U hU I _ _ fun x => ?_
  have key := (congrArg (res (abSections I) (hint x).ge) (hg (τ ∘ x))).symm.trans
    (res_alt_sum_res (abSections I) (hint x).ge
      (fun a => inter_le_reindex (fun k => U (σ k)) (τ ∘ x) a.succAbove)
      (fun a => g (τ ∘ (x ∘ a.succAbove))))
  simp only [mcomp_md, mcomp_mmk, res_res]
  refine key.symm.trans ?_
  exact (res_mcomp_congr V U hU I s (hcomp x) _ le_rfl).trans (res_id _ _)

end Elements

/-! ### The positive-degree vanishing -/

/-- **Stacks 01EP, positive degrees.** The positive-degree module-valued Čech cohomology of an
injective sheaf of modules vanishes. -/
@[stacks 01EP "positive degrees"]
public theorem isZero_cechComplex_homology_of_injective
    (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i)
    (I : SheafOfModules.{uM} R) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero ((cechComplex V U hU I).homology p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro s hs
  exact exists_md_eq V U hU I s hs

end

end Stacks.Cohomology.CechSheaf

end
