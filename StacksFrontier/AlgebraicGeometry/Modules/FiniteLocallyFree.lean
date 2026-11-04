module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Tactic.TFAE
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Finite locally free sheaves of modules

A sheaf of modules is *finite locally free* when it has local generators which are
simultaneously a local free basis and finite in number. A finite locally free sheaf of modules is
locally free, of finite type and of finite presentation. Over a commutative ring, finite
presentation together with flatness, with freeness of the localizations at all primes, or with
freeness of the localizations and local constancy of the rank, is equivalent to being finite
projective.

## Main definitions

* `Stacks.FiniteLocallyFree.IsFiniteLocallyFree` is finite local freeness of a sheaf of modules
  over an arbitrary site, a reducible spelling of the canonical class
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.
* `Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso` transports local generators data along an
  isomorphism of sheaves of modules.

## Main results

* `Stacks.FiniteLocallyFree.instIsLocallyFree`: a finite locally free sheaf of modules is
  locally free.
* `Stacks.FiniteLocallyFree.isFiniteType`: a finite locally free sheaf of modules is of finite
  type.
* `Stacks.FiniteLocallyFree.isFinitePresentation`: a finite locally free sheaf of modules is of
  finite presentation.
* `Stacks.FiniteLocallyFree.isLocallyFree_isFiniteType_isFinitePresentation`: the three together,
  for a sheaf of modules on a scheme.
* `Stacks.FiniteLocallyFree.instIsFiniteLocallyFreeFree`: a free sheaf of modules on a finite
  index type is finite locally free.
* `Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso`: finite local freeness only depends on
  the isomorphism class.
* `Stacks.FiniteLocallyFree.flat_of_free_localizedModule`: a module whose localization at every
  prime is free is flat.
* `Stacks.FiniteLocallyFree.module_tfae`: the equivalent characterizations of a finite projective
  module over a commutative ring.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace Stacks.FiniteLocallyFree

section Site

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is **finite locally free** if it has local generators data which is
both a local free basis and finite in each member of the covering.

This is a compatibility spelling of the canonical class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`: it is reducible, so instances and
hypotheses of either spelling are the same class to instance search. -/
abbrev IsFiniteLocallyFree (M : SheafOfModules.{u} R) : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, v₁, u₁} M

/-- Shrinking the indexing type of local generators data preserves finiteness of the generating
families. -/
instance isFiniteType_shrink {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData)
    [h : q.IsFiniteType] : q.shrink.IsFiniteType where
  isFiniteType i := h.isFiniteType i.2.choose

/-- Transport local generators data along an isomorphism of sheaves of modules, keeping the same
covering and pushing each generating family forward. -/
def localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (f.over (q.X i))

/-- Transporting local generators data along an isomorphism preserves finiteness. -/
instance isFiniteType_localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [IsIso f] (q : M.LocalGeneratorsData) [h : q.IsFiniteType] :
    (localGeneratorsDataOfIsIso f q).IsFiniteType where
  isFiniteType i :=
    have := h.isFiniteType i
    inferInstanceAs ((q.generators i).ofEpi (f.over (q.X i))).IsFiniteType

/-- Transporting local generators data along an isomorphism preserves local freeness. -/
instance isLocallyFreeData_localGeneratorsDataOfIsIso {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [IsIso f] (q : M.LocalGeneratorsData) [h : q.IsLocallyFreeData] :
    (localGeneratorsDataOfIsIso f q).IsLocallyFreeData where
  isIso i := by
    have h₁ : IsIso (q.generators i).π := h.isIso i
    have h₂ : IsIso (f.over (q.X i)) :=
      inferInstanceAs (IsIso ((SheafOfModules.overFunctor R (q.X i)).map f))
    change IsIso ((q.generators i).ofEpi (f.over (q.X i))).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- A finite locally free sheaf of modules is locally free. The instance is the one on the
canonical class `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`; this named form is kept
for explicit use. -/
theorem instIsLocallyFree (M : SheafOfModules.{u} R) [IsFiniteLocallyFree M] :
    M.IsLocallyFree :=
  inferInstance

/-- A finite locally free sheaf of modules is of finite type. -/
theorem isFiniteType (M : SheafOfModules.{u} R) [h : IsFiniteLocallyFree M] :
    M.IsFiniteType := by
  obtain ⟨q, -, hq⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨q, hq⟩

/-- Finite local freeness only depends on the isomorphism class of a sheaf of modules. -/
theorem IsFiniteLocallyFree.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [h : IsFiniteLocallyFree M] : IsFiniteLocallyFree N := by
  obtain ⟨q, hq, hq'⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨localGeneratorsDataOfIsIso e.hom q, inferInstance, inferInstance⟩

end Site

section Presentation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Locally free data which is of finite type gives a *finite* presentation: the associated
quasi-coherent data has finitely many generators and no relations at all. -/
instance isFinitePresentation_quasiCoherentData {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] [h : q.IsFiniteType] :
    q.quasiCoherentData.IsFinitePresentation where
  isFinite_presentation i :=
    { isFiniteType_generators := h.isFiniteType i
      isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }

/-- A finite locally free sheaf of modules is of finite presentation. -/
theorem isFinitePresentation (M : SheafOfModules.{u} R) [h : IsFiniteLocallyFree M] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq, hq'⟩ := h.exists_isFiniteLocallyFreeData
  exact ⟨q.shrink.quasiCoherentData, inferInstance⟩

end Presentation

section Free

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The local generators data of a free sheaf of modules coming from its canonical global basis
is of finite type as soon as the index type is finite. -/
instance isFiniteType_freeLocalGeneratorsData (I : Type u) [Finite I] :
    (SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData.IsFiniteType where
  isFiniteType _i := ⟨inferInstanceAs (Finite I)⟩

/-- A free sheaf of modules on a finite index type is finite locally free. -/
instance instIsFiniteLocallyFreeFree (I : Type u) [Finite I] :
    IsFiniteLocallyFree (SheafOfModules.free (R := R) I) :=
  ⟨(SheafOfModules.free.generatingSections I).localGeneratorsData, inferInstance, inferInstance⟩

end Free

section Scheme

/-- A finite locally free sheaf of modules on a scheme is locally free, of finite type and of
finite presentation. -/
theorem isLocallyFree_isFiniteType_isFinitePresentation {X : Scheme.{u}} (F : X.Modules)
    [IsFiniteLocallyFree (R := X.ringCatSheaf) F] :
    F.IsLocallyFree ∧ F.IsFiniteType ∧ F.IsFinitePresentation :=
  ⟨instIsLocallyFree F, isFiniteType F, isFinitePresentation F⟩

end Scheme

section Affine

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/-- A module whose localization at every prime is free is flat. -/
theorem flat_of_free_localizedModule
    (h : ∀ p : PrimeSpectrum R,
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)) :
    Module.Flat R M :=
  Module.flat_of_localized_maximal M fun P _ ↦
    have := h ⟨P, inferInstance⟩
    Module.Flat.trans R (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

/-- For a module `M` over a commutative ring `R`, the following are equivalent: `M` is flat and
finitely presented; `M` is finitely presented and its localization at every prime is free; `M` is
finite projective; `M` is finitely presented, its localization at every prime is free and its
rank function is locally constant. -/
theorem module_tfae :
    List.TFAE
      [Module.Flat R M ∧ Module.FinitePresentation R M,
        Module.FinitePresentation R M ∧ ∀ p : PrimeSpectrum R,
          Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M),
        Module.Projective R M ∧ Module.Finite R M,
        Module.FinitePresentation R M ∧ (∀ p : PrimeSpectrum R,
            Module.Free (Localization.AtPrime p.asIdeal)
              (LocalizedModule p.asIdeal.primeCompl M)) ∧
          IsLocallyConstant (Module.rankAtStalk (R := R) M)] := by
  tfae_have 1 → 2 := fun ⟨_, _⟩ ↦
    ⟨‹_›, Set.eq_univ_iff_forall.mp (Module.freeLocus_eq_univ (R := R) (M := M))⟩
  tfae_have 2 → 3 := fun ⟨_, h⟩ ↦
    ⟨Module.freeLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr h), inferInstance⟩
  tfae_have 3 → 1 := fun ⟨_, _⟩ ↦ ⟨inferInstance, Module.finitePresentation_of_projective R M⟩
  tfae_have 2 → 4 := fun ⟨_, h⟩ ↦
    have := flat_of_free_localizedModule R M h
    ⟨‹_›, h, Module.isLocallyConstant_rankAtStalk⟩
  tfae_have 4 → 2 := fun ⟨h₁, h₂, _⟩ ↦ ⟨h₁, h₂⟩
  tfae_finish

end Affine

end Stacks.FiniteLocallyFree

end
