module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.MapGluing
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# The torsor of generators of a rank-one module

For a ringed space `X` and a sheaf of `O_X`-modules `L` which is finite locally free of
rank one, the sections of `L` that trivialize it form a sheaf of sets on which the sheaf
of units of `O_X` acts simply transitively: a torsor under `O_X^*`.  This is the
construction underlying the first half of Stacks Tag 09NU.

## Main definitions

* `unitsAddCommGrpFunctor` sends a commutative ring to its group of units, written
  additively.
* `unitsSheaf` is the sheaf of units of a ringed space, written as a sheaf of abelian
  groups.
* `GeneratorSections` consists of the sections trivializing a module on an open.
* `GeneratorTorsor` packages a torsor under `unitsSheaf` together with the sectionwise
  identification of its sections with `GeneratorSections`, the compatibility of that
  identification with restriction, and its compatibility with the unit action.

## Main results

* `generatorSectionsPresheaf_isSheaf`: the generating condition is local, so the
  generator sections form a sheaf.
* `generatorSectionsAction_isPseudoTorsor`: two generators on the same open differ by a
  unique unit.
* `generatorSectionsAction_isTorsor` and `generatorTorsor`: the sheaf of generators,
  with its unit action, is a torsor.

## Implementation notes

The units sheaf is obtained by composing the structure sheaf with limit-preserving
functors.  Its sections over `U` are therefore definitionally `Additive O_X(U)ˣ`, and
`Multiplicative.ofAdd (Additive.ofMul f)` is the corresponding section of the
multiplicative group used by the torsor interface of Tag 02FO.

A section generates on `U` precisely when multiplication by its restriction induces a
bijection `O_X(V) → L(V)` for every open `V ≤ U`; this expresses that `O_U → L|_U` is an
isomorphism.  Locality of that condition is `scalar_smul_bijective_of_locally`, which
glues the inverse section by section through the sheaf axiom for `L`.

**The rank-one hypothesis is taken as a hypothesis, not derived.**  Tag 09NU's own
statement hypothesizes only that `L` is invertible
(`Stacks.SheafOfModules.IsInvertible`) and that every stalk of `O_X` is a local ring;
deducing `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1` from those two
is exactly clause 2 of Tag 0B8M.  The declarations here that need a local trivialization —
from `exists_local_unit_iso` onwards — carry `IsFiniteLocallyFreeOfRank L 1` as an instance
hypothesis instead, which is the weaker-to-use spelling, and **no declaration in this file
carries a Tag 09NU attribute**.  The restatement at the tag's own hypothesis is
`Stacks.Cohomology.Generators.generatorTorsorOfInvertible` of
`StacksFrontier/Topology/Sheaves/Cohomology/Torsors/GeneratorTorsorOfAnInvertibleModule.lean`,
which consumes clause 2 of Tag 0B8M through
`Stacks.InvertibleRankOneIff.isInvertible_iff_isFiniteLocallyFreeOfRank_one`.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

/-- The functor sending a commutative ring to its multiplicative group of units,
regarded as an additive commutative group. -/
public abbrev unitsAddCommGrpFunctor :
    Functor CommRingCat.{u} AddCommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

/-- The sheaf of units of a ringed space, written additively. -/
public abbrev unitsSheaf (X : RingedSpace.{u, u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    commGroupAddCommGroupEquivalence.functor).obj
      ((sheafCompose (Opens.grothendieckTopology X) CommMonCat.units).obj
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat CommMonCat)).obj X.sheaf))

/-- Sections of a module on `U` which trivialize it on `U`: multiplication by
the restricted section is bijective on every smaller open. -/
public abbrev GeneratorSections (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X) :=
  {s : L.val.obj (op U) // ∀ (V : Opens X) (h : V ≤ U),
    Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
      r • L.val.restrictₛₗ (homOfLE h).op s)}

/-- The generator torsor of a module, specified by its actual sections, restrictions,
and the action of units by scalar multiplication. -/
public structure GeneratorTorsor (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) extends
    Stacks.Cohomology.SheafTorsor.Torsor X (unitsSheaf X) where
  /-- Sections of the torsor are exactly the sections trivializing the module. -/
  sectionsEquiv (U : Opens X) : F.obj U ≃ GeneratorSections X L U
  /-- The section identifications commute with restriction. -/
  sectionsEquiv_restrict {U V : Opens X} (h : V ≤ U) (s : F.obj U) :
    (sectionsEquiv V (F.res h s)).val =
      L.val.restrictₛₗ (homOfLE h).op (sectionsEquiv U s).val
  /-- The torsor action corresponds to scalar multiplication by units. -/
  sectionsEquiv_smul (U : Opens X) (f : (X.presheaf.obj (op U))ˣ) (s : F.obj U) :
    (sectionsEquiv U (action.act (Multiplicative.ofAdd (Additive.ofMul f)) s)).val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op U)) (L.val.obj (op U)) _
        f.val (sectionsEquiv U s).val

/-- Two generators of a rank-one module differ by a unique unit. -/
theorem generators_unique_unit
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s t : M)
    (hs : Function.Bijective (fun r : R => r • s))
    (ht : Function.Bijective (fun r : R => r • t)) :
    ∃! f : Rˣ, (f : R) • s = t := by
  obtain ⟨r, hr⟩ := hs.2 t
  obtain ⟨q, hq⟩ := ht.2 s
  have hqr : q * r = 1 := hs.1 (by
    simp only [mul_smul, one_smul]
    calc
      q • (r • s) = q • t := congrArg (fun x : M => q • x) hr
      _ = s := hq)
  have hrq : r * q = 1 := by rw [mul_comm, hqr]
  let f : Rˣ := ⟨r, q, hrq, hqr⟩
  exact ⟨f, hr, fun g hg => Units.ext (hs.1 (hg.trans hr.symm))⟩

/-- A free module sheaf on a type with one element is the unit module sheaf. -/
noncomputable def freeUniqueIsoUnit
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {I : Type u} [Unique I]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.free (R := R) I ≅ SheafOfModules.unit R := by
  let hom := ((SheafOfModules.unit R).freeHomEquiv (I := I)).symm
    (fun _ => (SheafOfModules.unit R).unitHomEquiv (𝟙 (SheafOfModules.unit R)))
  let inv := SheafOfModules.ιFree (R := R) (default : I)
  refine ⟨hom, inv, ?_, ?_⟩
  · apply Limits.Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _
    intro i
    change SheafOfModules.ιFree (R := R) i ≫ hom ≫ inv =
      SheafOfModules.ιFree (R := R) i
    rw [← Category.assoc, ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Category.id_comp,
      hom, inv]
    exact congrArg (SheafOfModules.ιFree (R := R)) (Subsingleton.elim (default : I) i)
  · apply (SheafOfModules.unit R).unitHomEquiv.injective
    change (SheafOfModules.unit R).unitHomEquiv (inv ≫ hom) = _
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp [hom]

/-- A module which is finite locally free of rank one has, near every point, an
isomorphism with the unit module. -/
theorem exists_local_unit_iso (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1]
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty
      (SheafOfModules.unit ((structureSheaf X.sheaf).over U) ≅ L.over U) := by
  obtain ⟨q, hq, hRank⟩ :=
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens X) (J := Opens.grothendieckTopology X) L 1).exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨i, hi⟩ := hxcover
  let U := q.X i
  let I := (q.generators i).I
  obtain ⟨eI⟩ := hRank i
  let _ : Unique I := {
    default := eI.symm 0
    uniq := fun a => eI.injective (Subsingleton.elim (eI a) (eI (eI.symm 0)))
  }
  have hπ : IsIso (q.generators i).π := hq.isIso i
  let e : SheafOfModules.free (R := (structureSheaf X.sheaf).over U) I ≅ L.over U :=
    asIso (q.generators i).π
  refine ⟨U, hi, ⟨(freeUniqueIsoUnit (R := (structureSheaf X.sheaf).over U)
    (I := I)).symm ≪≫ e⟩⟩

/-- The local unit charts give actual generator sections on neighbourhoods. -/
theorem exists_generator_section (X : RingedSpace.{u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1]
    (x : X) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (GeneratorSections X L U) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := exists_local_unit_iso X L x
  let sU : L.val.obj (op U) :=
    (L.over U).unitHomEquiv e.hom |>.val (op (Over.mk (𝟙 U)))
  refine ⟨U, hxU, ⟨sU, ?_⟩⟩
  intro V hVU
  let R := structureSheaf X.sheaf
  let f : V ⟶ U := homOfLE hVU
  let eV : SheafOfModules.unit (R.over V) ≅ L.over V :=
    SheafOfModules.overMapUnitIso (R := R) f ≪≫
      (SheafOfModules.overMap R f).mapIso e
  let sV : L.val.obj (op V) :=
    (L.over V).unitHomEquiv eV.hom |>.val (op (Over.mk (𝟙 V)))
  have hsV : sV = L.val.restrictₛₗ f.op sU := by
    have hnat := e.hom.val.naturality
      ((Over.homMk (U := Over.mk f) f (by simp) :
        Over.mk f ⟶ Over.mk (𝟙 U)).op)
    have hlin := congrArg (fun q => q.hom) hnat
    have h := congrArg (fun g => g
      (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))) ) hlin
    change ((ModuleCat.restrictScalars
          (RingCat.Hom.hom ((R.over U).obj.map
            ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op)))).map
        (e.hom.val.app (op (Over.mk f))))
        (((SheafOfModules.unit (R.over U)).val.map
          ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op))
          (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) =
      ((L.over U).val.map
        ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op))
        ((e.hom.val.app (op (Over.mk (𝟙 U))))
          (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) at h
    have h' : (e.hom.val.app (op (Over.mk f)))
        (1 : (R.over U).obj.obj (op (Over.mk f))) =
      (L.val.map f.op) ((e.hom.val.app (op (Over.mk (𝟙 U))))
        (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) := by
      change ((ModuleCat.restrictScalars
            (RingCat.Hom.hom ((R.over U).obj.map
              ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op)))).map
          (e.hom.val.app (op (Over.mk f))))
          (((SheafOfModules.unit (R.over U)).val.map
            ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op))
            (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) =
        ((L.over U).val.map
          ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op))
          ((e.hom.val.app (op (Over.mk (𝟙 U))))
            (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) at h
      have hu : ((SheafOfModules.unit (R.over U)).val.map
          ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op))
          (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))) =
          (1 : (R.over U).obj.obj (op (Over.mk f))) := by
        change (PresheafOfModules.unit (R.over U).obj).map
          ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op)
          (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))) =
          (1 : (R.over U).obj.obj (op (Over.mk f)))
        exact PresheafOfModules.unit_map_one (R := (R.over U).obj)
          ((Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 U)).op)
      rw [hu] at h
      dsimp [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map'] at h
      change (e.hom.val.app (op (Over.mk f)))
          (1 : (R.over U).obj.obj (op (Over.mk f))) =
        (L.val.map f.op) ((e.hom.val.app (op (Over.mk (𝟙 U))))
          (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U))))) at h
      exact h
    change (eV.hom.val.app (op (Over.mk (𝟙 V))))
        (1 : (R.over V).obj.obj (op (Over.mk (𝟙 V)))) =
      (L.val.map f.op) ((e.hom.val.app (op (Over.mk (𝟙 U))))
        (1 : (R.over U).obj.obj (op (Over.mk (𝟙 U)))))
    have hcomp : (eV.hom.val.app (op (Over.mk (𝟙 V))))
        (1 : (R.over V).obj.obj (op (Over.mk (𝟙 V)))) =
      (e.hom.val.app (op (Over.mk f)))
        (1 : (R.over U).obj.obj (op (Over.mk f))) := by
      change (((SheafOfModules.overMap R f).map e.hom).val.app
        (op (Over.mk (𝟙 V))))
        (1 : (R.over V).obj.obj (op (Over.mk (𝟙 V)))) =
        (e.hom.val.app (op (Over.mk f)))
          (1 : (R.over U).obj.obj (op (Over.mk f)))
      rfl
    rw [hcomp]
    exact h'
  let m : ModuleCat.of (R.obj.obj (op V)) (R.obj.obj (op V)) ⟶
      ModuleCat.of (R.obj.obj (op V)) (L.val.obj (op V)) :=
    (SheafOfModules.evaluation (R.over V) (op (Over.mk (𝟙 V)))).map eV.hom
  have hm : Function.Bijective m := by
    have : IsIso m := Functor.map_isIso
      (SheafOfModules.evaluation (R.over V) (op (Over.mk (𝟙 V)))) eV.hom
    exact ConcreteCategory.bijective_of_isIso m
  have hfun :
      (fun r : R.obj.obj (op V) => r • L.val.restrictₛₗ f.op sU) = m := by
    funext r
    rw [← hsV]
    change r • sV = m r
    have hsmul := m.hom.map_smul r (1 : R.obj.obj (op V))
    have hone : m 1 = sV := by
      change (eV.hom.val.app (op (Over.mk (𝟙 V))))
        (1 : (R.over V).obj.obj (op (Over.mk (𝟙 V)))) = sV
      simp [sV, SheafOfModules.unitHomEquiv_apply_coe]
    rw [← hone]
    simpa using hsmul.symm
  rw [hfun]
  exact hm

/-- Multiplying a generator by a unit preserves the generator property. -/
theorem generator_smul_unit
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (s : M) (hs : Function.Bijective (fun r : R => r • s)) (f : Rˣ) :
    Function.Bijective (fun r : R => r • ((f : R) • s)) := by
  have hmul : Function.Bijective (fun r : R => r * (f : R)) := by
    constructor
    · intro a b h
      have h' := congrArg (fun x : R => x * (↑(f⁻¹) : R)) h
      simpa [mul_assoc] using h'
    · intro r
      exact ⟨r * (↑(f⁻¹) : R), by simp [mul_assoc]⟩
  constructor
  · intro a b hab
    apply hmul.1
    apply hs.1
    calc
      (a * (f : R)) • s = a • ((f : R) • s) := mul_smul a (f : R) s
      _ = b • ((f : R) • s) := hab
      _ = (b * (f : R)) • s := (mul_smul b (f : R) s).symm
  · intro x
    obtain ⟨r, hr⟩ := hs.2 x
    obtain ⟨a, ha⟩ := hmul.2 r
    refine ⟨a, ?_⟩
    calc
      a • ((f : R) • s) = (a * (f : R)) • s := (mul_smul a (f : R) s).symm
      _ = r • s := congrArg (fun z : R => z • s) ha
      _ = x := hr

/-- Scalar multiplication by a unit acts on the generator sections. -/
noncomputable def generatorSectionsSmul (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X)
    (f : ((structureSheaf X.sheaf).obj.obj (op U))ˣ)
    (s : GeneratorSections X L U) : GeneratorSections X L U := by
  refine ⟨(f : (structureSheaf X.sheaf).obj.obj (op U)) • s.val, ?_⟩
  intro V h
  let fV : ((structureSheaf X.sheaf).obj.obj (op V))ˣ :=
    Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom.toMonoidHom f
  have hs := s.property V h
  have heq :
      (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
        r • L.val.restrictₛₗ (homOfLE h).op
          ((f : (structureSheaf X.sheaf).obj.obj (op U)) • s.val)) =
      (fun r : (structureSheaf X.sheaf).obj.obj (op V) =>
        r • (fV : (structureSheaf X.sheaf).obj.obj (op V)) •
          L.val.restrictₛₗ (homOfLE h).op s.val) := by
    funext r
    simp [PresheafOfModules.restrictₛₗ_apply, fV]
  rw [heq]
  exact generator_smul_unit _ hs fV

/-- Two generator sections on the same open differ by a unique unit section. -/
theorem generatorSections_unique_unit (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) (U : Opens X)
    (s t : GeneratorSections X L U) :
    ∃! f : ((structureSheaf X.sheaf).obj.obj (op U))ˣ,
      generatorSectionsSmul X L U f s = t := by
  let _ : CommRing ((structureSheaf X.sheaf).obj.obj (op U)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (op U)))
  have hs : Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op U) =>
      r • s.val) := by
    simpa using s.property U le_rfl
  have ht : Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op U) =>
      r • t.val) := by
    simpa using t.property U le_rfl
  obtain ⟨f, hf, huniq⟩ := generators_unique_unit s.val t.val hs ht
  refine ⟨f, ?_, fun g hg => huniq g (congrArg Subtype.val hg)⟩
  exact Subtype.ext (by simpa [generatorSectionsSmul] using hf)

-- The semilinear restriction maps expand through universe-indexed categories.
/-- Restricting a generator section gives a generator section. -/
noncomputable def generatorSectionsRestrict (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    {U V : Opens X} (h : V ≤ U) (s : GeneratorSections X L U) :
    GeneratorSections X L V := by
  refine ⟨L.val.restrictₛₗ (homOfLE h).op s.val, ?_⟩
  intro W k
  have hgen := s.property W (k.trans h)
  have heq :
      (fun r : (structureSheaf X.sheaf).obj.obj (op W) =>
        r • L.val.restrictₛₗ (homOfLE k).op
          (L.val.restrictₛₗ (homOfLE h).op s.val)) =
      (fun r : (structureSheaf X.sheaf).obj.obj (op W) =>
        r • L.val.restrictₛₗ (homOfLE (k.trans h)).op s.val) := by
    funext r
    change r • L.val.map (homOfLE k).op (L.val.map (homOfLE h).op s.val) =
      r • L.val.map (homOfLE (k.trans h)).op s.val
    apply congrArg (fun m => r • m)
    rw [← L.val.map_comp_apply (homOfLE h).op (homOfLE k).op s.val]
    congr 1
  rw [heq]
  exact hgen

/-- The local generators form a presheaf before imposing the sheaf condition. -/
noncomputable def generatorSectionsPresheaf (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    Stacks.SpaceTorsor.PresheafOfSets X where
  obj U := GeneratorSections X L U
  res h := generatorSectionsRestrict X L h
  res_self U s := Subtype.ext (by
    change L.val.map (homOfLE (le_rfl : U ≤ U)).op s.val = s.val
    simp
    rfl)
  res_comp hWV hVU s := Subtype.ext (by
    change L.val.map (homOfLE hWV).op (L.val.map (homOfLE hVU).op s.val) =
      L.val.map (homOfLE (hWV.trans hVU)).op s.val
    rw [← L.val.map_comp_apply]
    congr 1)

/-- The additive sheaf underlying the structure sheaf. -/
noncomputable def ringSectionsAddSheaf (X : RingedSpace.{u, u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf

/-- The additive sheaf underlying a sheaf of modules. -/
noncomputable def moduleSectionsAddSheaf (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    TopCat.Sheaf AddCommGrpCat.{u} X := by
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := L.val.presheaf
  have hP : P.IsSheaf := by
    change Presheaf.IsSheaf (Opens.grothendieckTopology X) L.val.presheaf
    exact L.isSheaf
  exact ⟨P, hP⟩

/-- Restricting twice along `homOfLE` is restricting along the composite. -/
private theorem restrictₛₗ_restrictₛₗ_homOfLE {X : RingedSpace.{u, u}}
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) {U V W : Opens X} (h : V ≤ U) (k : W ≤ V)
    (m : L.val.obj (op U)) :
    L.val.restrictₛₗ (homOfLE k).op (L.val.restrictₛₗ (homOfLE h).op m) =
      L.val.restrictₛₗ (homOfLE (k.trans h)).op m := by
  change L.val.map (homOfLE k).op (L.val.map (homOfLE h).op m) =
    L.val.map (homOfLE (k.trans h)).op m
  rw [← L.val.map_comp_apply]
  congr 1

/-- Restrictions of a section to the two members of a cover agree on their intersection. -/
private theorem restrictₛₗ_inf_eq {X : RingedSpace.{u, u}}
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) {W : Opens X} {ι : Type u}
    (V : ι → Opens X) (hV : ∀ i, V i ≤ W) (m : L.val.obj (op W)) (i j : ι) :
    L.val.restrictₛₗ (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
        (L.val.restrictₛₗ (homOfLE (hV i)).op m) =
      L.val.restrictₛₗ (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
        (L.val.restrictₛₗ (homOfLE (hV j)).op m) := by
  rw [restrictₛₗ_restrictₛₗ_homOfLE, restrictₛₗ_restrictₛₗ_homOfLE]

-- Gluing the generating property unfolds semilinear module restrictions through the sheaf axiom.
/-- Bijectivity of multiplication by a section is local on an open cover. -/
theorem scalar_smul_bijective_of_locally
    (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    {W : Opens X} {ι : Type u} (V : ι → Opens X)
    (hV : ∀ i, V i ≤ W) (hcover : W = ⨆ i, V i)
    (s : L.val.obj (op W))
    (hs : ∀ i (Z : Opens X) (hZ : Z ≤ V i),
      Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op Z) =>
        r • L.val.restrictₛₗ (homOfLE (hZ.trans (hV i))).op s)) :
    Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op W) => r • s) := by
  classical
  subst W
  let R := structureSheaf X.sheaf
  let M := moduleSectionsAddSheaf X L
  have hM : TopCat.Presheaf.IsSheafUniqueGluing M.presheaf :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing M.presheaf).mp M.property
  constructor
  · intro r t hrt
    have hres (i : ι) : R.1.map (homOfLE (hV i)).op r =
        R.1.map (homOfLE (hV i)).op t := by
      apply (hs i (V i) le_rfl).1
      have h := congrArg (fun x => L.val.restrictₛₗ (homOfLE (hV i)).op x) hrt
      simpa [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.map_smul] using h
    have hc : TopCat.Presheaf.IsCompatible R.1 V
        (fun i => R.1.map (homOfLE (hV i)).op r) := by
      intro i j
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← R.1.map_comp, ← R.1.map_comp]
      congr 1
    obtain ⟨_, _, huniq⟩ := R.existsUnique_gluing V
      (fun i => R.1.map (homOfLE (hV i)).op r) hc
    exact (huniq r fun _ => rfl).trans (huniq t fun i => (hres i).symm).symm
  · intro t
    choose r hr using fun i => (hs i (V i) le_rfl).2
      (L.val.restrictₛₗ (homOfLE (hV i)).op t)
    have key (k : ι) (Z : Opens X) (hZ : Z ≤ V k) :
        R.1.map (homOfLE hZ).op (r k) • L.val.restrictₛₗ (homOfLE (hZ.trans (hV k))).op s =
        L.val.restrictₛₗ (homOfLE (hZ.trans (hV k))).op t := by
      rw [← restrictₛₗ_restrictₛₗ_homOfLE L (hV k) hZ s,
        ← restrictₛₗ_restrictₛₗ_homOfLE L (hV k) hZ t, ← hr k]
      exact (L.val.map_smul _ _ _).symm
    have hc : TopCat.Presheaf.IsCompatible R.1 V r := fun i j =>
      (hs i (V i ⊓ V j) inf_le_left).1
        ((key i _ inf_le_left).trans (key j _ inf_le_right).symm)
    obtain ⟨rW, hrW, _⟩ := R.existsUnique_gluing V r hc
    have htc : TopCat.Presheaf.IsCompatible M.presheaf V
        (fun i => M.presheaf.map (homOfLE (hV i)).op t) := fun i j =>
      restrictₛₗ_inf_eq L V hV t i j
    have hglue_rs : TopCat.Presheaf.IsGluing M.presheaf V
        (fun i => M.presheaf.map (homOfLE (hV i)).op t) (rW • s) := by
      intro i
      change L.val.map (homOfLE (hV i)).op (rW • s) =
        L.val.map (homOfLE (hV i)).op t
      rw [L.val.map_smul]
      change (R.1.map (homOfLE (hV i)).op rW) •
          L.val.map (homOfLE (hV i)).op s = L.val.map (homOfLE (hV i)).op t
      calc
        (R.1.map (homOfLE (hV i)).op rW) •
            L.val.map (homOfLE (hV i)).op s =
          r i • L.val.map (homOfLE (hV i)).op s := by
            convert congrArg (fun a => a • L.val.map (homOfLE (hV i)).op s) (hrW i) using 1
            congr 1
        _ = L.val.map (homOfLE (hV i)).op t := hr i
    obtain ⟨_, _, huniq⟩ := hM V (fun i => M.presheaf.map (homOfLE (hV i)).op t) htc
    exact ⟨rW, (huniq (rW • s) hglue_rs).trans (huniq t fun _ => rfl).symm⟩

-- Gluing the generating property uses sheaf uniqueness across the refinement cover.
/-- The presheaf of generator sections is a sheaf: the generating condition is local. -/
theorem generatorSectionsPresheaf_isSheaf (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    (generatorSectionsPresheaf X L).IsSheaf := by
  classical
  intro U ι V hV hcover
  subst U
  have hM : TopCat.Presheaf.IsSheafUniqueGluing (moduleSectionsAddSheaf X L).1 :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
      (moduleSectionsAddSheaf X L).1).mp (moduleSectionsAddSheaf X L).2
  constructor
  · intro a b hab
    have hc : TopCat.Presheaf.IsCompatible L.val.presheaf V
        (fun i => L.val.restrictₛₗ (homOfLE (hV i)).op a.val) := fun i j =>
      restrictₛₗ_inf_eq L V hV a.val i j
    obtain ⟨_, _, huniq⟩ := hM V
      (fun i => L.val.restrictₛₗ (homOfLE (hV i)).op a.val) hc
    have hb : TopCat.Presheaf.IsGluing L.val.presheaf V
        (fun i => L.val.restrictₛₗ (homOfLE (hV i)).op a.val) b.val := fun i =>
      congrArg Subtype.val (congrFun (congrArg Subtype.val hab) i).symm
    exact Subtype.ext ((huniq a.val fun _ => rfl).trans (huniq b.val hb).symm)
  · intro a
    let smod : ∀ i, L.val.obj (op (V i)) := fun i => (a.1 i).val
    have hc : TopCat.Presheaf.IsCompatible L.val.presheaf V smod := by
      intro i j
      change L.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op ((a.1 i).val) =
        L.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op ((a.1 j).val)
      exact congrArg Subtype.val
        (a.property i j (V i ⊓ V j) inf_le_left inf_le_right)
    obtain ⟨s, hs, _⟩ := hM V smod hc
    refine ⟨⟨s, ?_⟩, ?_⟩
    · intro W hWU
      apply scalar_smul_bijective_of_locally X L (fun i => W ⊓ V i)
        (fun i => inf_le_left) ?_ (L.val.restrictₛₗ (homOfLE hWU).op s) ?_
      · apply le_antisymm
        · intro x hx
          have hxU : x ∈ ⨆ i, V i := hWU hx
          rcases Opens.mem_iSup.mp hxU with ⟨i, hxi⟩
          exact Opens.mem_iSup.mpr ⟨i, ⟨hx, hxi⟩⟩
        · intro x hx
          rcases Opens.mem_iSup.mp hx with ⟨i, ⟨hxW, _⟩⟩
          exact hxW
      · intro i Z hZW
        have hZV : Z ≤ V i := hZW.trans inf_le_right
        have hZW' : Z ≤ W := hZW.trans inf_le_left
        have hrestrict : L.val.restrictₛₗ (homOfLE (hZW'.trans hWU)).op s =
            L.val.restrictₛₗ (homOfLE hZV).op (a.1 i).val := by
          rw [← restrictₛₗ_restrictₛₗ_homOfLE L (hV i) hZV s]
          exact congrArg _ (hs i)
        rw [restrictₛₗ_restrictₛₗ_homOfLE L hWU hZW' s, hrestrict]
        exact (a.1 i).property Z hZV
    · apply Subtype.ext
      funext i
      apply Subtype.ext
      exact hs i

/-- The unit sheaf acts on the presheaf of generator sections. -/
noncomputable def generatorSectionsAction (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    Stacks.SpaceTorsor.Action
      (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X))
      (generatorSectionsPresheaf X L) where
  act {U} f s := generatorSectionsSmul X L U
    (Additive.toMul (Multiplicative.toAdd f)) s
  one_act {U} s := by
    apply Subtype.ext
    change (1 : (structureSheaf X.sheaf).obj.obj (op U)) • s.val = s.val
    exact one_smul _ _
  mul_act {U} f g s := by
    let fu : ((structureSheaf X.sheaf).obj.obj (op U))ˣ :=
      Additive.toMul (Multiplicative.toAdd f)
    let gu : ((structureSheaf X.sheaf).obj.obj (op U))ˣ :=
      Additive.toMul (Multiplicative.toAdd g)
    apply Subtype.ext
    change ((fu : (structureSheaf X.sheaf).obj.obj (op U)) *
        (gu : (structureSheaf X.sheaf).obj.obj (op U))) • s.val =
      (fu : (structureSheaf X.sheaf).obj.obj (op U)) •
        ((gu : (structureSheaf X.sheaf).obj.obj (op U)) • s.val)
    exact mul_smul _ _ _
  res_act {U V} h f s := by
    apply Subtype.ext
    let fU : ((structureSheaf X.sheaf).obj.obj (op U))ˣ :=
      Additive.toMul (Multiplicative.toAdd f)
    let fV : ((structureSheaf X.sheaf).obj.obj (op V))ˣ :=
      Units.map ((structureSheaf X.sheaf).obj.map (homOfLE h).op).hom.toMonoidHom fU
    change L.val.restrictₛₗ (homOfLE h).op (fU.val • s.val) =
      fV.val • L.val.restrictₛₗ (homOfLE h).op s.val
    simp [PresheafOfModules.restrictₛₗ_apply, fU, fV]

/-- Local generators form simply transitive orbits under units. -/
theorem generatorSectionsAction_isPseudoTorsor (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf)) :
    (generatorSectionsAction X L).IsPseudoTorsor := by
  intro U hs
  constructor
  · rcases hs with ⟨s⟩
    exact ⟨s⟩
  · intro s t
    obtain ⟨f, hf, huniq⟩ := generatorSections_unique_unit X L U s t
    let g : (Stacks.Cohomology.SheafTorsor.underlyingPresheafOfGroups X (unitsSheaf X)).obj U :=
      Multiplicative.ofAdd (Additive.ofMul f)
    refine ⟨g, ?_, ?_⟩
    · exact hf
    · exact fun g' hg' => Multiplicative.ext (Additive.ext (huniq _ hg'))

/-- Local trivializations make every stalk of the generator presheaf nonempty. -/
theorem generatorSectionsAction_stalkNonempty (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    ∀ x : X, (generatorSectionsPresheaf X L).StalkNonempty x := by
  intro x
  obtain ⟨U, hxU, ⟨s⟩⟩ := exists_generator_section X L x
  exact ⟨U, hxU, ⟨s⟩⟩

/-- The generator presheaf with its unit action is a torsor before imposing the
sheaf condition. -/
theorem generatorSectionsAction_isTorsor (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    (generatorSectionsAction X L).IsTorsor :=
  ⟨generatorSectionsAction_isPseudoTorsor X L,
    generatorSectionsAction_stalkNonempty X L⟩

/-- The sheaf of generators of a module which is finite locally free of rank one is a
torsor under the sheaf of units, with the specified sectionwise identifications.

This is the construction Tag 09NU calls the generator torsor, under the rank-one
hypothesis rather than invertibility; see the module's implementation notes. -/
public def generatorTorsor (X : RingedSpace.{u, u})
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens X)
      (J := Opens.grothendieckTopology X) L 1] :
    GeneratorTorsor X L := by
  refine {
    F := ⟨generatorSectionsPresheaf X L,
      generatorSectionsPresheaf_isSheaf X L⟩
    action := generatorSectionsAction X L
    isTorsor := generatorSectionsAction_isTorsor X L
    sectionsEquiv U := Equiv.refl _
    sectionsEquiv_restrict h s := ?_
    sectionsEquiv_smul U f s := ?_ }
  · rfl
  · rfl

end Stacks.Cohomology.Generators

end
