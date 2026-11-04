module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# The explicit Čech complexes of a sheaf of modules, over the ring of sections

Let `X` be a topological space carrying a sheaf of rings `R`, let `V` be an open subset, let
`U : ι → Opens X` be a cover of `V` and let `I` be a sheaf of `R`-modules. Every intersection
`U_{i_0 … i_p}` of members of the cover is contained in `V`, so its sections of `I` are a module
over the ring of sections `R(V)`; the explicit Čech cochains of Tags 01FH–01FI are therefore
`R(V)`-modules, the Čech differential is `R(V)`-linear, and the alternating cochains form an
`R(V)`-submodule. This file builds the three resulting complexes of `R(V)`-modules — the usual,
the alternating and, for a linearly ordered index type, the ordered one — together with the
`R(V)`-linear comparisons of Tag 01FJ between them.

## Main definitions

* `Stacks.Cohomology.CechSheaf.sectionsModuleOfLE`: sections over an open contained in `V`, as a
  module over `R(V)`.
* `Stacks.Cohomology.CechSheaf.cochainModule` and
  `Stacks.Cohomology.CechSheaf.ordCochainModule`: the `R(V)`-module structures on the explicit
  Čech cochains and on the ordered Čech cochains.
* `Stacks.Cohomology.CechSheaf.alternatingSubmodule`: the alternating cochains of Tag 01FH as an
  `R(V)`-submodule.
* `Stacks.Cohomology.CechSheaf.cechModuleComplex`,
  `Stacks.Cohomology.CechSheaf.alternatingModuleComplex` and
  `Stacks.Cohomology.CechSheaf.orderedModuleComplex`: the three explicit Čech complexes, as
  complexes of `R(V)`-modules.
* `Stacks.Cohomology.CechSheaf.alternatingModuleInclusion`: the `R(V)`-linear inclusion of the
  alternating Čech complex into the usual one.
* `Stacks.Cohomology.CechSheaf.piLinear` and `Stacks.Cohomology.CechSheaf.cLinearEquiv`:
  restriction of an alternating cochain to the strictly increasing tuples, as an `R(V)`-linear
  map and as an `R(V)`-linear isomorphism.

## Main results

* `Stacks.Cohomology.CechSheaf.cochain_smul_apply` and
  `Stacks.Cohomology.CechSheaf.ordCochain_smul_apply`: the scalar action on a cochain is, at
  every tuple, the action of `R(V)` on the sections over the corresponding intersection.
* `Stacks.Cohomology.CechSheaf.res_smul`: restriction of sections between opens contained in `V`
  is `R(V)`-linear; `Stacks.Cohomology.CechSheaf.cechD_smul` and
  `Stacks.Cohomology.CechSheaf.ordD_smul` are the two Čech differentials.
* `CechCochains.pi_cechD_of_isAlternating`: on an alternating cochain, restricting the Čech
  differential to the strictly increasing tuples is the ordered Čech differential.
* `Stacks.Cohomology.CechSheaf.alternatingIsoOrderedModuleComplex` and
  `Stacks.Cohomology.CechSheaf.orderedIsoAlternatingModuleComplex`: **Tag 01FJ,
  `R(V)`-linearly.** The alternating and the ordered Čech complex of `R(V)`-modules are
  isomorphic as cochain complexes.

## Implementation notes

**The cochains are the ones of Tag 01FH, carrying extra structure.** The degree-`p` term is
`ModuleCat.of _ (CechCochains.Cochain U (abSections I) p)` and the alternating term is
`ModuleCat.of _ (alternatingSubmodule V U hU I p)`, whose carrier is *the same type* as
`CechCochains.alternatingSubgroup U (abSections I) p` — `alternatingSubmodule` adds `smul_mem'`
to that subgroup. So the abelian-group-level theory of Tags 01FH, 01FI and 01FJ applies to these
cochains verbatim, and only the linearity of each map has to be supplied.

**Where the module structure comes from.** `sectionsModuleOfLE` takes the module structure that
`sectionsPresheaf V I`, the presheaf of `R(V)`-modules on the slice over `V`, already carries at
the object `Over.mk (homOfLE h)`. Choosing it rather than building a fresh restriction of scalars
is what makes `res_smul` one application of `map_smul`, and it is also the structure the
module-valued Čech complex `Stacks.Cohomology.CechSheaf.cechComplex` of the slice site carries,
so no comparison of scalar actions is needed when the two models are identified.

**The module structures are `def`s, not instances.** They depend on the covering equation `hU`
and on a proof that an open is contained in `V`, neither of which instance search can supply, so
they are introduced by `letI` where they are used and every statement about the scalar action
names them.

**The index family.** Nothing beyond the covering equation is used about `U`; a client needing
affineness or finiteness supplies it where it uses it.

**No `@[stacks]` attribute.** Tags 01FH, 01FI and 01FJ already have their carriers in
`StacksDraft.Topology.Sheaves.Cohomology.Cech`; the declarations here state the same things with
an `R(V)`-module structure added, which is a refinement rather than a different clause.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis (res)

universe uX uR uM

attribute [local implicit_reducible] CechCochains.Cochain
attribute [local implicit_reducible] CechCochains.OrdCochain

namespace CechCochains

/-- On an alternating cochain the Čech differential agrees with the ordered Čech differential:
restricting `d s` to the strictly increasing tuples is the ordered differential of the
restriction of `s`. -/
theorem pi_cechD_of_isAlternating {Y : TopCat} {κ : Type*} [LinearOrder κ] (W : κ → Opens Y)
    (G : TopCat.Presheaf AddCommGrpCat Y) (p : ℕ)
    (t : Cochain W G p) (ht : IsAlternating W G t) :
    pi W G (p + 1) (cechD W G p t) = ordD W G p (pi W G p t) := by
  have h : cechD W G p t = c W G (p + 1) (ordD W G p (pi W G p t)) := by
    rw [c_chainMap W G p (pi W G p t), c_pi_of_isAlternating W G p t ht]
  rw [h, pi_c]

end CechCochains

namespace Stacks.Cohomology.CechSheaf

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uM}
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)

/-! ### Sections over an open contained in the covered one -/

/-- Sections of a sheaf of modules over an open contained in `V` form a module over the ring of
sections `R(V)`: the module structure the slice site over `V` carries. -/
@[instance_reducible]
def sectionsModuleOfLE {W : Opens X} (h : W ≤ V) :
    Module (SectionRing R V) (ToType ((abSections I).obj (op W))) :=
  inferInstanceAs (Module _
    (ToType ((sectionsPresheaf V I).obj (op (Over.mk (homOfLE h))))))

/-- Restriction of sections between two opens contained in `V` is `R(V)`-linear. -/
theorem res_smul {W W' : Opens X} (h : W ≤ V) (h' : W' ≤ V) (hle : W ≤ W')
    (a : SectionRing R V) (t : ToType ((abSections I).obj (op W'))) :
    letI := sectionsModuleOfLE V I h
    letI := sectionsModuleOfLE V I h'
    res (abSections I) hle (a • t) = a • res (abSections I) hle t :=
  let := sectionsModuleOfLE V I h
  let := sectionsModuleOfLE V I h'
  map_smul ((sectionsPresheaf V I).map
    (Over.homMk (homOfLE hle) (Subsingleton.elim _ _) :
      (Over.mk (homOfLE h) : Over V) ⟶ Over.mk (homOfLE h')).op).hom a t

/-- `CechCochains.restr`, the restriction map used by the explicit Čech complexes, is
`R(V)`-linear between opens contained in `V`. -/
theorem restr_smul {W W' : Opens X} (h : W ≤ V) (h' : W' ≤ V) (hle : W ≤ W')
    (a : SectionRing R V) (t : ToType ((abSections I).obj (op W'))) :
    letI := sectionsModuleOfLE V I h
    letI := sectionsModuleOfLE V I h'
    CechCochains.restr (X := TopCat.of X) (abSections I) hle (a • t) =
      a • CechCochains.restr (X := TopCat.of X) (abSections I) hle t :=
  res_smul V I h h' hle a t

/-- Transport of sections along any morphism of opens contained in `V` is `R(V)`-linear: in the
poset of opens such a morphism is an inclusion. -/
theorem map_smul_of_le {W W' : Opens X} (h : W ≤ V) (h' : W' ≤ V) (g : W ⟶ W')
    (a : SectionRing R V) (t : ToType ((abSections I).obj (op W'))) :
    letI := sectionsModuleOfLE V I h
    letI := sectionsModuleOfLE V I h'
    ConcreteCategory.hom ((abSections I).map g.op) (a • t) =
      a • ConcreteCategory.hom ((abSections I).map g.op) t :=
  res_smul V I h h' (leOfHom g) a t

include hU in
/-- The intersection selected by a nonempty tuple of indices is contained in the covered open. -/
theorem cechInter_le_covered {m : ℕ} (x : Fin (m + 1) → ι) :
    CechCochains.inter (X := TopCat.of X) U x ≤ V :=
  (iInf_le (fun k => U (x k)) 0).trans (by rw [hU]; exact le_iSup U (x 0))

/-! ### The Čech cochains as modules -/

/-- Degree-`p` Čech cochains of `I` with respect to `U` form a module over `R(V)`, tuplewise. -/
@[instance_reducible]
def cochainModule (p : ℕ) :
    Module (SectionRing R V) (CechCochains.Cochain (X := TopCat.of X) U (abSections I) p) :=
  letI : ∀ i : Fin (p + 1) → ι, Module (SectionRing R V)
      (ToType ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U i)))) :=
    fun i => sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
  inferInstanceAs (Module _ (∀ i : Fin (p + 1) → ι,
    ToType ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U i)))))

/-- The scalar action on a Čech cochain is, at every tuple, the action of `R(V)` on the sections
over the intersection selected by that tuple. -/
theorem cochain_smul_apply (p : ℕ) (a : SectionRing R V)
    (s : CechCochains.Cochain (X := TopCat.of X) U (abSections I) p) (i : Fin (p + 1) → ι) :
    letI := cochainModule V U hU I p
    letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
    (a • s) i = a • s i := rfl

/-- The identification of sections along a permutation of the index tuple is `R(V)`-linear. -/
theorem permIso_smul {p : ℕ} (i : Fin (p + 1) → ι) (σ : Equiv.Perm (Fin (p + 1)))
    (a : SectionRing R V)
    (x : ToType ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U i)))) :
    letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
    letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU (i ∘ σ))
    CechCochains.permIso (X := TopCat.of X) U (abSections I) i σ (a • x) =
      a • CechCochains.permIso (X := TopCat.of X) U (abSections I) i σ x :=
  map_smul_of_le V I (cechInter_le_covered V U hU (i ∘ σ)) (cechInter_le_covered V U hU i)
    (eqToHom (CechCochains.inter_comp_perm (X := TopCat.of X) U i σ)) a x

/-- The signed sum of restrictions along the omission maps, as in the Čech differentials, commutes
with the action of `R(V)`. -/
private theorem signed_sum_restr_smul {p : ℕ} (a : SectionRing R V) (i : Fin (p + 2) → ι)
    (t : ∀ j : Fin (p + 2), ToType
      ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U (i ∘ j.succAbove))))) :
    letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (X := TopCat.of X) (abSections I) (CechCochains.inter_le_omit U i j)
          (letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU (i ∘ j.succAbove));
            a • t j) =
      a • ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (X := TopCat.of X) (abSections I) (CechCochains.inter_le_omit U i j)
          (t j) := by
  let := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  let := sectionsModuleOfLE V I (cechInter_le_covered V U hU (i ∘ j.succAbove))
  rw [restr_smul V I (cechInter_le_covered V U hU i)
      (cechInter_le_covered V U hU (i ∘ j.succAbove))
      (CechCochains.inter_le_omit (X := TopCat.of X) U i j) a]
  exact (smul_comm _ _ _).symm

/-- The Čech differential is `R(V)`-linear. -/
theorem cechD_smul (p : ℕ) (a : SectionRing R V)
    (s : CechCochains.Cochain (X := TopCat.of X) U (abSections I) p) :
    letI := cochainModule V U hU I p
    letI := cochainModule V U hU I (p + 1)
    CechCochains.cechD (X := TopCat.of X) U (abSections I) p (a • s) =
      a • CechCochains.cechD (X := TopCat.of X) U (abSections I) p s := by
  let := cochainModule V U hU I p
  let := cochainModule V U hU I (p + 1)
  funext i
  let := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
  rw [cochain_smul_apply V U hU I (p + 1) a _ i]
  exact signed_sum_restr_smul V U hU I a i fun j => s (i ∘ j.succAbove)

/-- The alternating Čech cochains of Tag 01FH form an `R(V)`-submodule of all cochains.

Its carrier is the carrier of `CechCochains.alternatingSubgroup`, so the two coercions to types
agree. -/
def alternatingSubmodule (p : ℕ) :
    letI := cochainModule V U hU I p
    Submodule (SectionRing R V) (CechCochains.Cochain (X := TopCat.of X) U (abSections I) p) :=
  letI := cochainModule V U hU I p
  { CechCochains.alternatingSubgroup (X := TopCat.of X) U (abSections I) p with
    smul_mem' := fun a s hs => by
      refine ⟨fun i hi => ?_, fun i b b' hbb' => ?_⟩
      · let := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
        rw [cochain_smul_apply V U hU I p a s i, hs.1 i hi, smul_zero]
      · let := sectionsModuleOfLE V I (cechInter_le_covered V U hU i)
        let := sectionsModuleOfLE V I (cechInter_le_covered V U hU (i ∘ Equiv.swap b b'))
        rw [cochain_smul_apply V U hU I p a s _, cochain_smul_apply V U hU I p a s i,
          hs.2 i b b' hbb', permIso_smul V U hU I i (Equiv.swap b b') a, smul_neg] }

/-! ### The usual and the alternating complex of modules -/

/-- The degree-`p` term of the usual explicit Čech complex of `R(V)`-modules: all cochains. -/
@[implicit_reducible]
def cechCochainModuleObj (p : ℕ) : ModuleCat.{uM} (SectionRing R V) :=
  letI := cochainModule V U hU I p
  ModuleCat.of _ (CechCochains.Cochain (X := TopCat.of X) U (abSections I) p)

/-- The degree-`p` term of the alternating Čech complex of `R(V)`-modules. -/
@[implicit_reducible]
def alternatingCochainModuleObj (p : ℕ) : ModuleCat.{uM} (SectionRing R V) :=
  letI := cochainModule V U hU I p
  ModuleCat.of _ (alternatingSubmodule V U hU I p)

/-- The Čech differential as an `R(V)`-linear map. -/
def cechDLinear (p : ℕ) :
    letI := cochainModule V U hU I p
    letI := cochainModule V U hU I (p + 1)
    CechCochains.Cochain (X := TopCat.of X) U (abSections I) p →ₗ[SectionRing R V]
      CechCochains.Cochain (X := TopCat.of X) U (abSections I) (p + 1) :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU I (p + 1)
  { toFun := CechCochains.cechD (X := TopCat.of X) U (abSections I) p
    map_add' := map_add _
    map_smul' := cechD_smul V U hU I p }

/-- The Čech differential restricted to the alternating cochains, as an `R(V)`-linear map. -/
def alternatingDLinear (p : ℕ) :
    letI := cochainModule V U hU I p
    letI := cochainModule V U hU I (p + 1)
    alternatingSubmodule V U hU I p →ₗ[SectionRing R V] alternatingSubmodule V U hU I (p + 1) :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU I (p + 1)
  (cechDLinear V U hU I p).restrict
    (fun s hs => CechCochains.cechD_mem_alternating (X := TopCat.of X) U (abSections I) p s hs)

/-- The Čech differential, as a morphism of `R(V)`-modules. -/
@[implicit_reducible]
def cechModuleDiff (p : ℕ) :
    cechCochainModuleObj V U hU I p ⟶ cechCochainModuleObj V U hU I (p + 1) :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU I (p + 1)
  ModuleCat.ofHom (cechDLinear V U hU I p)

/-- The alternating Čech differential, as a morphism of `R(V)`-modules. -/
@[implicit_reducible]
def alternatingModuleDiff (p : ℕ) :
    alternatingCochainModuleObj V U hU I p ⟶ alternatingCochainModuleObj V U hU I (p + 1) :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU I (p + 1)
  ModuleCat.ofHom (alternatingDLinear V U hU I p)

/-- The degreewise inclusion of the alternating cochains into all cochains, as a morphism of
`R(V)`-modules. -/
@[implicit_reducible]
def alternatingModuleSubtype (p : ℕ) :
    alternatingCochainModuleObj V U hU I p ⟶ cechCochainModuleObj V U hU I p :=
  letI := cochainModule V U hU I p
  ModuleCat.ofHom (alternatingSubmodule V U hU I p).subtype

/-- Two consecutive Čech differentials compose to zero. -/
theorem cechModuleDiff_comp (p : ℕ) :
    cechModuleDiff V U hU I p ≫ cechModuleDiff V U hU I (p + 1) = 0 := by
  ext s
  exact CechCochains.cechD_cechD (X := TopCat.of X) U (abSections I) p s

/-- Two consecutive alternating Čech differentials compose to zero. -/
theorem alternatingModuleDiff_comp (p : ℕ) :
    alternatingModuleDiff V U hU I p ≫ alternatingModuleDiff V U hU I (p + 1) = 0 := by
  ext s
  exact Subtype.ext (CechCochains.cechD_cechD (X := TopCat.of X) U (abSections I) p s.1)

/-- The usual explicit Čech complex of a sheaf of modules, as a complex of `R(V)`-modules. -/
@[implicit_reducible]
def cechModuleComplex : CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  CochainComplex.of (cechCochainModuleObj V U hU I) (cechModuleDiff V U hU I)
    (cechModuleDiff_comp V U hU I)

/-- **Tag 01FH, `R(V)`-linearly.** The alternating Čech complex of a sheaf of modules, as a
complex of `R(V)`-modules. -/
@[implicit_reducible]
def alternatingModuleComplex : CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  CochainComplex.of (alternatingCochainModuleObj V U hU I) (alternatingModuleDiff V U hU I)
    (alternatingModuleDiff_comp V U hU I)

/-- The degree-`p` term of the usual explicit Čech complex of `R(V)`-modules. -/
@[simp]
theorem cechModuleComplex_X (p : ℕ) :
    (cechModuleComplex V U hU I).X p = cechCochainModuleObj V U hU I p := rfl

/-- The degree-`p` term of the alternating Čech complex of `R(V)`-modules. -/
@[simp]
theorem alternatingModuleComplex_X (p : ℕ) :
    (alternatingModuleComplex V U hU I).X p = alternatingCochainModuleObj V U hU I p := rfl

/-- The consecutive differentials of the usual explicit Čech complex of `R(V)`-modules. -/
@[simp]
theorem cechModuleComplex_d (p : ℕ) :
    (cechModuleComplex V U hU I).d p (p + 1) = cechModuleDiff V U hU I p :=
  CochainComplex.of_d _ _ p

/-- The consecutive differentials of the alternating Čech complex of `R(V)`-modules. -/
@[simp]
theorem alternatingModuleComplex_d (p : ℕ) :
    (alternatingModuleComplex V U hU I).d p (p + 1) = alternatingModuleDiff V U hU I p :=
  CochainComplex.of_d _ _ p

/-- **Tag 01FH, `R(V)`-linearly.** The inclusion of the alternating Čech complex of
`R(V)`-modules into the usual one: in each degree the inclusion of the submodule of alternating
cochains. -/
def alternatingModuleInclusion :
    alternatingModuleComplex V U hU I ⟶ cechModuleComplex V U hU I :=
  CochainComplex.ofHom (fun p => alternatingModuleSubtype V U hU I p) (fun p => by
    rw [cechModuleComplex_d, alternatingModuleComplex_d]
    ext s
    rfl)

/-- In every degree the `R(V)`-linear inclusion is the inclusion of the submodule of alternating
cochains. -/
@[simp]
theorem alternatingModuleInclusion_f (p : ℕ) :
    (alternatingModuleInclusion V U hU I).f p = alternatingModuleSubtype V U hU I p := rfl

/-! ### The ordered complex of modules -/

section Ordered

variable [LinearOrder ι]

/-- Degree-`p` ordered Čech cochains of `I` with respect to `U` form a module over `R(V)`,
tuplewise. -/
@[instance_reducible]
def ordCochainModule (p : ℕ) :
    Module (SectionRing R V) (CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p) :=
  letI : ∀ i : CechCochains.OrdIndex (I := ι) p, Module (SectionRing R V)
      (ToType ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U i.1)))) :=
    fun i => sectionsModuleOfLE V I (cechInter_le_covered V U hU i.1)
  inferInstanceAs (Module _ (∀ i : CechCochains.OrdIndex (I := ι) p,
    ToType ((abSections I).obj (op (CechCochains.inter (X := TopCat.of X) U i.1)))))

/-- The scalar action on an ordered Čech cochain is, at every strictly increasing tuple, the
action of `R(V)` on the sections over the intersection selected by that tuple. -/
theorem ordCochain_smul_apply (p : ℕ) (a : SectionRing R V)
    (s : CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p)
    (i : CechCochains.OrdIndex (I := ι) p) :
    letI := ordCochainModule V U hU I p
    letI := sectionsModuleOfLE V I (cechInter_le_covered V U hU i.1)
    (a • s) i = a • s i := rfl

/-- The ordered Čech differential is `R(V)`-linear. -/
theorem ordD_smul (p : ℕ) (a : SectionRing R V)
    (s : CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p) :
    letI := ordCochainModule V U hU I p
    letI := ordCochainModule V U hU I (p + 1)
    CechCochains.ordD (X := TopCat.of X) U (abSections I) p (a • s) =
      a • CechCochains.ordD (X := TopCat.of X) U (abSections I) p s := by
  let := ordCochainModule V U hU I p
  let := ordCochainModule V U hU I (p + 1)
  funext i
  let := sectionsModuleOfLE V I (cechInter_le_covered V U hU i.1)
  rw [ordCochain_smul_apply V U hU I (p + 1) a _ i]
  exact signed_sum_restr_smul V U hU I a i.1
    fun j => s ⟨i.1 ∘ j.succAbove, CechCochains.strictMono_omit i.2 j⟩

/-- The ordered Čech differential as an `R(V)`-linear map. -/
def ordDLinear (p : ℕ) :
    letI := ordCochainModule V U hU I p
    letI := ordCochainModule V U hU I (p + 1)
    CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p →ₗ[SectionRing R V]
      CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) (p + 1) :=
  letI := ordCochainModule V U hU I p
  letI := ordCochainModule V U hU I (p + 1)
  { toFun := CechCochains.ordD (X := TopCat.of X) U (abSections I) p
    map_add' := map_add _
    map_smul' := ordD_smul V U hU I p }

/-- The degree-`p` term of the ordered Čech complex of `R(V)`-modules. -/
@[implicit_reducible]
def ordCochainModuleObj (p : ℕ) : ModuleCat.{uM} (SectionRing R V) :=
  letI := ordCochainModule V U hU I p
  ModuleCat.of _ (CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p)

/-- The ordered Čech differential, as a morphism of `R(V)`-modules. -/
@[implicit_reducible]
def ordModuleDiff (p : ℕ) :
    ordCochainModuleObj V U hU I p ⟶ ordCochainModuleObj V U hU I (p + 1) :=
  letI := ordCochainModule V U hU I p
  letI := ordCochainModule V U hU I (p + 1)
  ModuleCat.ofHom (ordDLinear V U hU I p)

/-- Two consecutive ordered Čech differentials compose to zero. -/
theorem ordModuleDiff_comp (p : ℕ) :
    ordModuleDiff V U hU I p ≫ ordModuleDiff V U hU I (p + 1) = 0 := by
  ext s
  exact CechCochains.ordD_ordD (X := TopCat.of X) U (abSections I) p s

/-- **Tag 01FI, `R(V)`-linearly.** The ordered Čech complex of a sheaf of modules, as a complex
of `R(V)`-modules. -/
@[implicit_reducible]
def orderedModuleComplex : CochainComplex (ModuleCat.{uM} (SectionRing R V)) ℕ :=
  CochainComplex.of (ordCochainModuleObj V U hU I) (ordModuleDiff V U hU I)
    (ordModuleDiff_comp V U hU I)

/-- The degree-`p` term of the ordered Čech complex of `R(V)`-modules. -/
@[simp]
theorem orderedModuleComplex_X (p : ℕ) :
    (orderedModuleComplex V U hU I).X p = ordCochainModuleObj V U hU I p := rfl

/-- The consecutive differentials of the ordered Čech complex of `R(V)`-modules. -/
@[simp]
theorem orderedModuleComplex_d (p : ℕ) :
    (orderedModuleComplex V U hU I).d p (p + 1) = ordModuleDiff V U hU I p :=
  CochainComplex.of_d _ _ p

/-- Restriction of an alternating cochain to the strictly increasing tuples, as an `R(V)`-linear
map. -/
def piLinear (p : ℕ) :
    letI := cochainModule V U hU I p
    letI := ordCochainModule V U hU I p
    alternatingSubmodule V U hU I p →ₗ[SectionRing R V]
      CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p :=
  letI := cochainModule V U hU I p
  letI := ordCochainModule V U hU I p
  { toFun := fun s => CechCochains.pi (X := TopCat.of X) U (abSections I) p s.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- `Stacks.Cohomology.CechSheaf.piLinear` is bijective: this is Tag 01FJ, whose inverse is
signed sorting of the index tuples. -/
theorem piLinear_bijective (p : ℕ) : Function.Bijective (piLinear V U hU I p) :=
  (CechCochains.cAddEquiv (X := TopCat.of X) U (abSections I) p).symm.bijective

/-- **Tag 01FJ, `R(V)`-linearly, degreewise.** The alternating Čech cochains are the ordered Čech
cochains, as `R(V)`-modules. -/
def cLinearEquiv (p : ℕ) :
    letI := cochainModule V U hU I p
    letI := ordCochainModule V U hU I p
    alternatingSubmodule V U hU I p ≃ₗ[SectionRing R V]
      CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p :=
  letI := cochainModule V U hU I p
  letI := ordCochainModule V U hU I p
  LinearEquiv.ofBijective (piLinear V U hU I p) (piLinear_bijective V U hU I p)

/-- **Tag 01FJ, `R(V)`-linearly.** The alternating Čech complex of `R(V)`-modules is the ordered
Čech complex of `R(V)`-modules; in each degree the isomorphism restricts a cochain to the
strictly increasing tuples. -/
def alternatingIsoOrderedModuleComplex :
    alternatingModuleComplex V U hU I ≅ orderedModuleComplex V U hU I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (cLinearEquiv V U hU I p).toModuleIso) (fun {i j} hij => by
      obtain rfl : i + 1 = j := hij
      rw [orderedModuleComplex_d, alternatingModuleComplex_d]
      exact ModuleCat.hom_ext <| LinearMap.ext fun s =>
        (CechCochains.pi_cechD_of_isAlternating (Y := TopCat.of X) U (abSections I) i
          s.1 s.2).symm)

/-- **Tag 01FJ, `R(V)`-linearly.** The ordered Čech complex of `R(V)`-modules is the alternating
Čech complex of `R(V)`-modules. -/
def orderedIsoAlternatingModuleComplex :
    orderedModuleComplex V U hU I ≅ alternatingModuleComplex V U hU I :=
  (alternatingIsoOrderedModuleComplex V U hU I).symm

end Ordered

end

end Stacks.Cohomology.CechSheaf

end
