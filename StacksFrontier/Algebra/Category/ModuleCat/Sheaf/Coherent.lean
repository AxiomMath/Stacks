module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves of modules

A sheaf of modules on a ringed space is *coherent* when it is of finite type and the relations
among every finite family of sections over every open subset are locally finitely generated.
This file defines the coherence predicate and the full subcategory of coherent sheaves, and
proves closure properties of coherence and of finite type.

## Main definitions

* `Stacks.SheafOfModules.IsCoherent` is the coherence predicate on a sheaf of modules over a
  ringed space.
* `Stacks.SheafOfModules.coherentModules` is coherence packaged as an `ObjectProperty`, and
  `Stacks.SheafOfModules.CoherentModules` is the corresponding full subcategory, the category
  denoted `Coh(O_X)`.
* `Stacks.SheafOfModules.freeGeneratingSections` is the standard basis of a free sheaf of
  modules, viewed as a family of generating sections, and
  `Stacks.SheafOfModules.zeroGeneratingSections` is the empty family generating a zero sheaf.
* `Stacks.SheafOfModules.bindLocalGeneratorsData` glues local generators of the restrictions of
  a sheaf of modules to the members of a covering family into local generators of the sheaf
  itself. It is the family-of-generators analogue of
  `SheafOfModules.QuasicoherentData.bind`.

## Main results

* `Stacks.SheafOfModules.over_epi` and `Stacks.SheafOfModules.over_mono`: restriction to an
  object of the site preserves epimorphisms and monomorphisms.
* `Stacks.SheafOfModules.isFiniteType_of_epi'` and `Stacks.SheafOfModules.isFiniteType_of_iso`:
  being of finite type passes to quotients, hence is invariant under isomorphism.
* `Stacks.SheafOfModules.isFiniteType_free`: a finite free sheaf of modules is of finite type,
  and `Stacks.SheafOfModules.isFiniteType_of_isZero`: so is a zero sheaf.
* `Stacks.SheafOfModules.isFiniteType_of_coversTop`: being of finite type is local on the base.
* `Stacks.SheafOfModules.isCoherent_of_mono`: a finite type subsheaf of a coherent sheaf of
  modules is coherent.
* `Stacks.SheafOfModules.isCoherent_of_isZero`: a zero sheaf of modules is coherent.
* `Stacks.SheafOfModules.coherentModules` contains the zero object and is closed under
  isomorphisms, two of the five closure conditions defining a weak Serre class.

## Implementation notes

The restriction lemmas and the finite type closure lemmas are stated over an arbitrary site,
not only over the opens of a topological space: they are facts about
`SheafOfModules.overFunctor`, which exists for any site. The coherence predicate itself is
stated for a ringed space, following the source.

These lemmas are stated over an equi-universe site: the site, its hom level, the ring and the
modules all share the single universe `u`, whereas Mathlib keeps `SheafOfModules.IsFiniteType`
polymorphic in three independent universes. So `isFiniteType_of_epi'` and its companions
elaborate at `IsFiniteType.{u, u, u}` and cannot be applied over a ringed site with independent
universes, where the goal is `IsFiniteType.{w, v, u}`. In particular they do not serve the
setting of sites with three independent universes, which in any case uses a separate
presheaf-level coherence predicate. Decoupling those universes is the change that would make
this section reusable there.

Finite type over the slice site `(Opens.grothendieckTopology X).over U` is used as finite type
of the restriction as an `𝒪_U`-module on `U`; this identification is not proved here. It is
true, and it is why the restriction lemmas say what one wants. The identification
`(M.over U).sections ≃ M.val.obj (op U)` is
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`, with `evalOver` and `mkOver`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension`; a morphism out of the
sections of `M` over `U` is built with those.

The space, the sheaf of rings, the sections and the index types of the free modules all live in
one common universe `u`. Condition (2) of coherence quantifies over maps out of
`SheafOfModules.free I` on the slice site `(Opens.grothendieckTopology X).over U`, so stating it
requires `Limits.kernel` to exist there, which requires the sheafification instances
`HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}` and
`((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}`. These are
available at every universe `u`, not only at `Type 0`, once
`Mathlib.Algebra.Category.Grp.FilteredColimits` supplies the filtered colimits from which the
concrete sheafification of `AddCommGrpCat` is built; that is why this import is here.

Commutativity of the structure sheaf is not needed for any statement here, so `R` is allowed to
be a sheaf of not necessarily commutative rings.

Condition (2) of coherence is stated as a condition on maps `free I ⟶ M.over U` out of a finite
free module rather than on finite families of sections of `M` over `U`. By
`SheafOfModules.freeHomEquiv` these are the same data: a map `φ : free I ⟶ M.over U`
corresponds to the family `(M.over U).freeHomEquiv φ` of sections, and the associated map of a
family `s` is `(M.over U).freeHomEquiv.symm s`, so quantifying over `φ` is quantifying over
finite families of sections as in the source.

The declarations live in the `Stacks.SheafOfModules` namespace rather than in `SheafOfModules`,
so that this file can be co-imported with the rest of the library.

`isFiniteType_of_epi'` carries a prime because
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension` declares an
`isFiniteType_of_epi` in this same namespace. That version is more general: it is stated at
three independent universes where this one is equi-universe. The two have different argument
shapes (instance versus explicit finite-type hypothesis), so replacing this copy by that one
requires adapting the call sites.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace SheafOfModules ZeroObject

universe u

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Restriction to an object of the site preserves monomorphisms: on sections it is a
reindexing, so it preserves injectivity. -/
theorem over_mono {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Mono p] (U : C) :
    Mono (p.over U) :=
  (SheafOfModules.forget (R.over U)).mono_of_mono_map (f := p.over U)
    (PresheafOfModules.mono_of_injective fun _ =>
      PresheafOfModules.injective_of_mono ((SheafOfModules.forget R).map p) _)

/-- Restriction to an object of the site preserves epimorphisms: `SheafOfModules.overFunctor`
is a left adjoint, so it preserves colimits and therefore epimorphisms. -/
theorem over_epi [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (p : M ⟶ N) [Epi p] (U : C) :
    Epi (p.over U) := by
  have h : (SheafOfModules.pushforward.{u} (𝟙 (R.over U))).PreservesEpimorphisms := by
    have : PreservesColimitsOfShape WalkingSpan
        (SheafOfModules.pushforward.{u} (𝟙 (R.over U))) := inferInstance
    infer_instance
  exact h.preserves p

section FiniteTypeClosure

variable [HasBinaryProducts C]
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Being of finite type passes to quotients: if `M` is of finite type and `p : M ⟶ N` is an
epimorphism, then `N` is of finite type. This is the sheaf of modules form of the statement
that a quotient of a finitely generated module is finitely generated. -/
theorem isFiniteType_of_epi' {M N : SheafOfModules.{u} R} (p : M ⟶ N)
    [M.IsFiniteType] [Epi p] : N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have he : ∀ i, Epi (p.over (σ.X i)) := fun i => over_epi p (σ.X i)
  have hfin : ∀ i, (σ.generators i).IsFiniteType := fun i => hσ.isFiniteType i
  exact { exists_localGeneratorsData :=
    ⟨{ I := σ.I, X := σ.X, coversTop := σ.coversTop,
       generators := fun i => (σ.generators i).ofEpi (p.over (σ.X i)) },
     { isFiniteType := fun i => inferInstance }⟩ }

/-- Being of finite type is invariant under isomorphism.

This is not the same statement as `Stacks.AlgebraicGeometry.DerivedPushforward.isFiniteType_of_iso`
of `StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic`: that one is polymorphic in the
three universes of the site, the sections and the modules where this one has them equal, so
merging the two in either direction would narrow a statement. -/
theorem isFiniteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType :=
  isFiniteType_of_epi' e.hom

end FiniteTypeClosure

section Free

variable [HasBinaryProducts C]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules generated by finitely many global sections is of finite type: the
trivial covering of the site witnesses it. -/
theorem isFiniteType_of_generatingSections {M : SheafOfModules.{u} R}
    (G : M.GeneratingSections) [G.IsFiniteType] : M.IsFiniteType :=
  { exists_localGeneratorsData := ⟨G.localGeneratorsData,
      { isFiniteType := fun _ => ⟨inferInstanceAs (Finite G.I)⟩ }⟩ }

/-- The standard basis of a free sheaf of modules, as a family of generating sections. -/
@[ega "0 5.5.5"]
noncomputable def freeGeneratingSections (I : Type u) :
    (free I : SheafOfModules.{u} R).GeneratingSections where
  I := I
  s := (free I : SheafOfModules.{u} R).freeHomEquiv (𝟙 _)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

/-- The standard generating sections of a free sheaf of modules on a finite type are finite. -/
instance (I : Type u) [Finite I] : (freeGeneratingSections (R := R) I).IsFiniteType where
  finite := inferInstanceAs (Finite I)

/-- A finite free sheaf of modules is of finite type. -/
instance isFiniteType_free (I : Type u) [Finite I] :
    (free I : SheafOfModules.{u} R).IsFiniteType :=
  isFiniteType_of_generatingSections (freeGeneratingSections I)

omit [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- Restriction to an object of the site preserves zero objects. -/
theorem over_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) (U : C) :
    IsZero (M.over U) :=
  Functor.map_isZero (SheafOfModules.pushforward.{u} (𝟙 (R.over U))) hM

/-- The empty family generates a zero sheaf of modules. -/
noncomputable def zeroGeneratingSections {M : SheafOfModules.{u} R} (hM : IsZero M) :
    M.GeneratingSections where
  I := PEmpty.{u + 1}
  s := fun x => x.elim
  epi := ⟨fun g h _ => hM.eq_of_src g h⟩

/-- The empty family of generating sections of a zero sheaf of modules is finite. -/
instance {M : SheafOfModules.{u} R} (hM : IsZero M) :
    (zeroGeneratingSections hM).IsFiniteType where
  finite := inferInstanceAs (Finite PEmpty.{u + 1})

/-- A zero sheaf of modules is of finite type. -/
theorem isFiniteType_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) : M.IsFiniteType :=
  isFiniteType_of_generatingSections (zeroGeneratingSections hM)

end Free

section Locality

variable [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), HasSheafify ((J.over Y).over Z) AddCommGrpCat.{u}]
  [∀ (Y : C) (Z : Over Y), ((J.over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Local generators of the restrictions of `M` to the members of a covering family glue to
local generators of `M` itself: the datum indexed by `⟨i, j⟩` is that of `D i` at `j`,
transported from the iterated slice `(M.over (Xc i)).over ((D i).X j)` to the object
`((D i).X j).left` along `Over.iteratedSliceEquiv`. This is the family-of-generators analogue
of `SheafOfModules.QuasicoherentData.bind`, and the transport is what makes finiteness of
generators a local condition on the base. -/
noncomputable def bindLocalGeneratorsData (M : SheafOfModules.{u} R) {I : Type u}
    (Xc : I → C) (hX : J.CoversTop Xc)
    (D : Π i, (M.over (Xc i)).LocalGeneratorsData) :
    M.LocalGeneratorsData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i ↦ (D i).coversTop)
  generators i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).generators i.2).map e.inverse (.refl _)).ofEpi
      (e.fullyFaithfulFunctor.preimageIso
        (by exact e.counitIso.app ((M.over (Xc i.1)).over ((D i.1).X i.2)))).hom

/-- Gluing finite local generators yields finite local generators: both transporting along an
equivalence and pushing along an epimorphism keep the index type of a family of generating
sections. -/
instance bindLocalGeneratorsData_isFiniteType (M : SheafOfModules.{u} R) {I : Type u}
    (Xc : I → C) (hX : J.CoversTop Xc)
    (D : Π i, (M.over (Xc i)).LocalGeneratorsData) [hD : ∀ i, (D i).IsFiniteType] :
    (bindLocalGeneratorsData M Xc hX D).IsFiniteType where
  isFiniteType i := by
    have := (hD i.1).isFiniteType i.2
    exact ⟨inferInstanceAs (Finite ((D i.1).generators i.2).I)⟩

/-- **Being of finite type is local on the base.** If the members of a covering family of the
terminal object all have finite type restrictions of `M`, then `M` is of finite type.

Mathlib has this for quasicoherence (`SheafOfModules.IsQuasicoherent.of_coversTop`) but not for
finite type, because it has no `bind` for families of generating sections. -/
theorem isFiniteType_of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (Xc : I → C) (hX : J.CoversTop Xc) [∀ i, (M.over (Xc i)).IsFiniteType] :
    M.IsFiniteType := by
  choose D hD using fun i => SheafOfModules.IsFiniteType.exists_localGeneratorsData (M.over (Xc i))
  exact { exists_localGeneratorsData :=
    ⟨bindLocalGeneratorsData M Xc hX D, bindLocalGeneratorsData_isFiniteType M Xc hX D⟩ }

end Locality

end Site

section RingedSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A sheaf of modules `M` over a ringed space is *coherent* if

1. `M` is of finite type, and
2. for every open `U` and every finite index type `I`, the kernel of every `O_U`-module map
   `free I ⟶ M|_U` — equivalently, of the associated map of every finite family of sections of
   `M` over `U` — is of finite type. -/
@[stacks 01BV "the coherence predicate", ega "0 5.3.7"]
class IsCoherent (M : SheafOfModules.{u} R) : Prop where
  /-- A coherent sheaf of modules is of finite type. -/
  isFiniteType : M.IsFiniteType
  /-- The kernel of the associated map of any finite family of sections over any open is of
  finite type. -/
  kernel_isFiniteType : ∀ (U : Opens X) (I : Type u) (_ : Finite I)
    (φ : (free I : SheafOfModules.{u} (R.over U)) ⟶ M.over U), (kernel φ).IsFiniteType

attribute [instance] IsCoherent.isFiniteType

/-- Coherence as a property of objects of the category of sheaves of modules. -/
abbrev coherentModules (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    ObjectProperty (SheafOfModules.{u} R) :=
  fun M => IsCoherent M

/-- The full subcategory `Coh(O_X)` of coherent sheaves of modules over a ringed space. -/
@[stacks 01BV "the category Coh"]
abbrev CoherentModules (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :=
  (coherentModules R).FullSubcategory

/-- The underlying sheaf of modules of an object of `CoherentModules R` is coherent. -/
instance (M : CoherentModules R) : IsCoherent M.obj := M.property

/-- Let `ι : N ⟶ M` be a monomorphism and `φ` a map from a free module to `N|_U`. If the kernel of
`φ ≫ ι|_U` is of finite type, then so is the kernel of `φ`, since the two kernels agree. -/
theorem isFiniteType_kernel_of_mono {M N : SheafOfModules.{u} R} (ι : N ⟶ M) [Mono ι]
    (U : Opens X) {I : Type u} (φ : (free I : SheafOfModules.{u} (R.over U)) ⟶ N.over U)
    (h : (kernel (φ ≫ ι.over U)).IsFiniteType) : (kernel φ).IsFiniteType :=
  have : Mono (ι.over U) := over_mono ι U
  isFiniteType_of_iso.{u} (M := kernel (φ ≫ ι.over U)) (N := kernel φ)
    (kernelCompMono φ (ι.over U))

/-- A finite type subsheaf of a coherent sheaf of modules is coherent: the second condition of
coherence passes to subsheaves, because a map out of a free module into the subsheaf has the
same kernel as its composite into the ambient sheaf. -/
@[stacks 01BY "(1)"]
theorem isCoherent_of_mono {M N : SheafOfModules.{u} R} (ι : N ⟶ M) [Mono ι]
    [IsCoherent M] [N.IsFiniteType] : IsCoherent N where
  isFiniteType := inferInstance
  kernel_isFiniteType U I hI φ :=
    isFiniteType_kernel_of_mono ι U φ (IsCoherent.kernel_isFiniteType U I hI (φ ≫ ι.over U))

/-- A zero sheaf of modules is coherent: it is of finite type, and every map into its
restriction is zero, so the kernels in question are the finite free modules themselves. -/
theorem isCoherent_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) : IsCoherent M where
  isFiniteType := isFiniteType_of_isZero.{u} (M := M) hM
  kernel_isFiniteType U I hI φ := by
    rw [(over_isZero hM U).eq_zero_of_tgt φ]
    exact isFiniteType_of_iso.{u} (M := (free I : SheafOfModules.{u} (R.over U)))
      (N := kernel (0 : (free I : SheafOfModules.{u} (R.over U)) ⟶ M.over U))
      kernelZeroIsoSource.symm

/-- The coherent sheaves of modules contain a zero object. -/
instance : (coherentModules R).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isCoherent_of_isZero (isZero_zero _)⟩

/-- Coherence of sheaves of modules is invariant under isomorphism. -/
instance : (coherentModules R).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM :=
    have : IsCoherent M := hM
    have _hft : N.IsFiniteType := isFiniteType_of_iso.{u} (M := M) (N := N) e
    isCoherent_of_mono (M := M) (N := N) e.inv

end RingedSpace

end Stacks.SheafOfModules
