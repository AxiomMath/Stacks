module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify

/-!
# An invertible sheaf of modules is of finite presentation, and the converse half of Tag 0B8M

Let `(X, 𝒪_X)` be a ringed space all of whose structure-sheaf stalks are local rings, and let `L`
be an invertible sheaf of `𝒪_X`-modules. This file proves the converse direction of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M): such an `L` is finite locally free
of rank one. Together with the unconditional direction, already proved as
`Stacks.SheafOfModules.isInvertible_of_isFiniteLocallyFreeOfRank_one` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOneLocal.lean`, this gives the tag's
characterization `isInvertible_iff_isFiniteLocallyFreeOfRank_one`.

Stacks' proof of the converse is a chain of four steps. Three of them were already in this
library: the stalks of an invertible sheaf of modules are invertible modules
(`Stacks.SheafOfModules.module_invertible_grpStalk`), hence free of rank one over a local ring
(`Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv`, Tag 0AFW), and a finitely presented sheaf
of modules with free stalk at a point is free near that point
(`Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free`, Tag 0B8J). The step that was
missing is the third one, "`L` is of finite presentation", and it is the main content of this
file; it is stated over an arbitrary site and is independent of Tag 0B8M.

## Main definitions

* `Stacks.SheafOfModules.piUnitToFree` and `Stacks.SheafOfModules.freeToPiUnit`: the two
  morphisms identifying a finite product of copies of the structure sheaf with the finite free
  sheaf of modules on the lifted index type.

## Main results

* `Stacks.SheafOfModules.exists_isFinite_presentation_of_retract`: a retract of a finite free
  sheaf of modules has a finite presentation, with the retraction itself as the generators and
  the complementary idempotent as the relations.
* `Stacks.SheafOfModules.exists_isFinite_presentation_of_isSplitMono_pi`: the same for a split
  subobject of a finite product of copies of the structure sheaf, which is the shape in which
  Tag 0B8N (b) delivers its conclusion.
* `Stacks.SheafOfModules.isFinitePresentation_of_coversTop`: finite presentation is local on a
  covering family of the terminal object.
* `Stacks.SheafOfModules.isFinitePresentation_of_isInvertible`: **an invertible sheaf of modules
  is of finite presentation.** This is the missing step of Tag 0B8M's converse, and the only
  result here that is about invertibility over a general site.
* `Stacks.SheafOfModules.ringStalk_smul_eq` and
  `Stacks.SheafOfModules.nonempty_stalk_linearEquiv_finsupp`: the two stalks of the structure
  sheaf of a ringed space act on the stalk of a sheaf of modules through the same scalar
  multiplication, so freeness of rank one over one of them gives freeness of rank one over the
  other.
* `Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible` (in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse`): the converse
  direction of Tag 0B8M, in the form of local triviality.
* `Stacks.SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one` (in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Characterization`): **Tag
  0B8M**, the characterization of invertibility on a ringed space whose structure-sheaf stalks
  are local rings.

## Implementation notes

**Finite presentation from a retraction, not from a cokernel.** Stacks reads the conclusion of
Tag 0B8K/0B8N — that `L` is locally a direct summand of a finite free module — as a finite
presentation by exhibiting `L` as the cokernel of `1 - e` on the finite free module, `e` being the
idempotent of the splitting. Mathlib's `SheafOfModules.Presentation` does not ask for a cokernel
diagram: it asks for generating sections of `M` and generating sections of the kernel of the
resulting `free ι ⟶ M`. For a retract `s ≫ r = 𝟙 M` of `free ι` both are immediate and no
cokernel comparison is needed. The retraction `r` is a split epi, hence generates; and
`1 - r ≫ s`, which kills `r`, factors through `kernel r` by a map which `kernel.ι r` *splits*
(because `kernel.ι r ≫ r = 0` makes `kernel.ι r ≫ (1 - r ≫ s) = kernel.ι r`), hence is a split
epi and generates the kernel. Only `Preadditive` and `HasKernels` are used, both of which hold
for `SheafOfModules` under `HasWeakSheafify` alone, so nothing in this part needs
`SheafOfModules R` to be abelian.

**Why the product has to be turned into a coproduct by hand.** Tag 0B8N (b)
(`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`) produces a split mono into
`∏ᶜ (fun _ : Fin n ↦ unit R)`, whereas `SheafOfModules.GeneratingSections` is a family of
sections indexed by a `Type w`, i.e. a morphism out of `SheafOfModules.free ι = ∐ (fun _ : ι ↦
unit R)`. The two differ in two ways: product versus coproduct, and the index type `Fin n`, which
lives in `Type 0`, versus an index type in the module universe `w`. Going through
`biproduct.isoProduct` and `Sigma.whiskerEquiv` fails, because the `HasColimit` instance that
`SheafOfModules.free` was defined with and the one that the biproduct machinery supplies are
different instances, so the two colimit objects are not interchangeable without unfolding
`getColimitCocone`, which is not exposed. Instead `piUnitToFree` and `freeToPiUnit` are written
down directly from the coordinates `Stacks.SheafOfModules.freeProj` and
`SheafOfModules.ιFree` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkFreeCover.lean`, and
only the composite `piUnitToFree ≫ freeToPiUnit = 𝟙` is proved, which is all that transporting a
split mono needs. The index type is `ULift.{w} (Fin n)`, matching the `ULift.{u} (Fin r)` that
Tag 0B8J already uses.

**Where the covering family comes from.** Tag 0B8N (b) gives, for *each* object `U`, a covering
family of `U` trivializing `L` in the above sense, while `SheafOfModules.QuasicoherentData` asks
for a single family covering the terminal object. The family used here is the union over all
objects `U : C` of the families produced at `U`, indexed by `Σ U : C, Idx U`; it covers the
terminal object because for each `U` the sieve generated by the family at `U` is already covering
and is contained in `Sieve.ofObjects` of the union (`Sieve.ofArrows_le_ofObjects` composed with
`Sieve.ofObjects_mono`). The resulting index type lives in `Type (max u v)` and is brought back
into the universe of the site by `SheafOfModules.QuasicoherentData.shrink`, for which
`isFinitePresentation_shrink` records that finiteness of the local presentations survives.

**The two stalks of the structure sheaf.** `Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
  X x` is `X.presheaf.stalk x`,
a filtered colimit taken in `CommRingCat`, and it is the ring over which the first two steps of
the converse are stated; Tag 0B8J instead phrases its hypothesis with `R.presheaf.stalk x` for
`R` the structure sheaf viewed in `RingCat`, which is the *same* filtered colimit taken in
`RingCat`. The comparison of the two is not built here: it is
`SemilinearStalk.commStalkRingEquiv` of
`StacksFrontier/Topology/Sheaves/Functors/Module/SemilinearStalk.lean`, together with its germ
formula `SemilinearStalk.commStalkRingEquiv_germ`, both universe-polymorphic.
`SemilinearStalk.comm_smul_eq` in the same file is the statement that the two scalar actions on
the stalk of a presheaf of modules agree, but it carries no universe parameter — the
`PresheafOfModules` variable of its section introduced none, so every universe in it is fixed at
`0` and it cannot be applied at the universe `u` of a `RingedSpace.{u, u}`. So `ringStalk_smul_eq`
proves that statement here by germ induction, which is in any case what is needed: it is stated
for the module structure `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, the instance
  in which the first two steps
of the converse are phrased, rather than for Mathlib's, the two being equal but not
definitionally so (`Stacks.SheafOfModules.stalkModule_eq`). Both actions are pinned down by the
same germ formula, `PresheafOfModules.germ_ringCat_smul` for the `RingCat` one and
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul` for the `CommRingCat` one.

**Universes.** Nothing is narrowed. The general results are stated for a site `C : Type u` with
`Category.{v} C` and a module universe `w` unrelated to either, matching
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleSummandSheafify.lean`. The ringed-space
results are stated for `AlgebraicGeometry.RingedSpace.{u, u}` and `SheafOfModules.{u}`, which is
the single universe the site `Opens X` forces and is the setting of
Tag 01CB and of Tag 0B8J.

**What is still not proved.** The parenthetical remark of Tag 0B8M, that the converse fails for a
general ringed space, is not addressed here; see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOneLocal.lean` for why the pinned
Mathlib cannot supply a witness.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory Limits Opposite SheafOfModules

universe v u w

namespace Stacks.SheafOfModules

/-! ### A retract of a finite free sheaf of modules is of finite presentation -/

section Retract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The generating sections of `N` named by a split epimorphism `free ι ⟶ N`. -/
private noncomputable abbrev generatingSectionsOfIsSplitEpi {ι : Type w} {N : SheafOfModules.{w} R}
    (f : free ι ⟶ N) [IsSplitEpi f] : N.GeneratingSections where
  I := ι
  s := N.freeHomEquiv f
  epi := by rw [Equiv.symm_apply_apply]; infer_instance

/-- **A retract of a finite free sheaf of modules has a finite presentation.**

The retraction `r` is a split epimorphism, so the family of sections it names generates `M`. The
endomorphism `1 - r ≫ s` of `free ι` composes to zero with `r`, hence factors through
`kernel r` through a morphism which `kernel.ι r` splits; so that morphism is a split
epimorphism and the family of sections it names generates `kernel r`. Both families are indexed
by `ι`, which is finite. -/
theorem exists_isFinite_presentation_of_retract {ι : Type w} [Finite ι]
    {M : SheafOfModules.{w} R} (s : M ⟶ free ι) (r : free ι ⟶ M) (h : s ≫ r = 𝟙 M) :
    ∃ p : M.Presentation, p.IsFinite := by
  have hre : IsSplitEpi r := IsSplitEpi.mk' ⟨s, h⟩
  let σ := generatingSectionsOfIsSplitEpi r
  have hπ : σ.π = r := M.freeHomEquiv.symm_apply_apply r
  have hsπ : s ≫ σ.π = 𝟙 M := by rw [hπ]; exact h
  have hker : (𝟙 (free (R := R) ι) - σ.π ≫ s) ≫ σ.π = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsπ, Category.comp_id, sub_self]
  have hk : kernel.ι σ.π ≫ kernel.lift σ.π _ hker = 𝟙 (kernel σ.π) := by
    refine (cancel_mono (kernel.ι σ.π)).mp ?_
    rw [Category.assoc, Category.id_comp, kernel.lift_ι, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, kernel.condition, zero_comp, sub_zero]
  have hke : IsSplitEpi (kernel.lift σ.π _ hker) := IsSplitEpi.mk' ⟨kernel.ι σ.π, hk⟩
  exact ⟨{ generators := σ, relations := generatingSectionsOfIsSplitEpi (kernel.lift σ.π _ hker) },
    { isFiniteType_generators := ⟨inferInstanceAs (Finite ι)⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite ι)⟩ }⟩

/-- A finite product of copies of the structure sheaf, mapped into the finite free sheaf of
modules on the lifted index type by assembling the coproduct inclusions against the product
projections. -/
noncomputable def piUnitToFree (n : ℕ) :
    (∏ᶜ fun _ : Fin n ↦ unit R) ⟶ free (ULift.{w} (Fin n)) :=
  ∑ j : Fin n, Pi.π (fun _ : Fin n ↦ unit R) j ≫ ιFree (ULift.up j)

/-- The finite free sheaf of modules on the lifted index type, mapped into a finite product of
copies of the structure sheaf by its coordinate projections. -/
noncomputable def freeToPiUnit (n : ℕ) :
    free (R := R) (ULift.{w} (Fin n)) ⟶ ∏ᶜ fun _ : Fin n ↦ unit R :=
  Pi.lift fun j : Fin n ↦ freeProj (ULift.up j)

/-- A finite product of copies of the structure sheaf is a retract of the finite free sheaf of
modules on the lifted index type. The two are in fact isomorphic, but only this one of the two
composites is needed. -/
lemma piUnitToFree_comp_freeToPiUnit (n : ℕ) :
    piUnitToFree (R := R) n ≫ freeToPiUnit n = 𝟙 (∏ᶜ fun _ : Fin n ↦ unit R) := by
  refine Pi.hom_ext _ _ fun k ↦ ?_
  rw [piUnitToFree, freeToPiUnit, Category.assoc, Pi.lift_comp_π, Category.id_comp,
    Preadditive.sum_comp]
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ k →
      (Pi.π (fun _ : Fin n ↦ unit R) j ≫ ιFree (R := R) (ULift.up j)) ≫
        freeProj (ULift.up k) = 0 := fun j _ hj ↦ by
    rw [Category.assoc, ιFree_comp_freeProj_of_ne (fun hu ↦ hj (congrArg ULift.down hu)),
      comp_zero]
  rw [Finset.sum_eq_single k hz fun hk ↦ absurd (Finset.mem_univ k) hk, Category.assoc,
    ιFree_comp_freeProj_self, Category.comp_id]

/-- **A split subobject of a finite product of copies of the structure sheaf has a finite
presentation.** This is the form in which Tag 0B8N (b) delivers its conclusion. -/
theorem exists_isFinite_presentation_of_isSplitMono_pi {n : ℕ} {M : SheafOfModules.{w} R}
    (s : M ⟶ ∏ᶜ fun _ : Fin n ↦ unit R) [IsSplitMono s] :
    ∃ p : M.Presentation, p.IsFinite := by
  refine exists_isFinite_presentation_of_retract (s ≫ piUnitToFree n)
    (freeToPiUnit n ≫ retraction s) ?_
  rw [Category.assoc, ← Category.assoc (piUnitToFree n), piUnitToFree_comp_freeToPiUnit,
    Category.id_comp]
  exact IsSplitMono.id s

end Retract

/-! ### Finite presentation is a local condition -/

section Locality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Shrinking the indexing type of quasi-coherent data preserves finiteness of the local
presentations, since the shrunk data reuses the original presentations. -/
instance isFinitePresentation_shrink {M : SheafOfModules.{w} R} (q : M.QuasicoherentData)
    [h : q.IsFinitePresentation] : q.shrink.IsFinitePresentation where
  isFinite_presentation i := h.isFinite_presentation i.2.choose

/-- **Finite presentation is a local condition.** A sheaf of modules whose restriction to each
member of a covering family of the terminal object has a finite presentation is of finite
presentation. The index type of the family is arbitrary; it is brought into the universe of the
site by `SheafOfModules.QuasicoherentData.shrink`. -/
theorem isFinitePresentation_of_coversTop {M : SheafOfModules.{w} R} {I : Type*} (X : I → C)
    (hX : J.CoversTop X) (h : ∀ i, ∃ p : (M.over (X i)).Presentation, p.IsFinite) :
    M.IsFinitePresentation := by
  let q : M.QuasicoherentData :=
    { I := I
      X := X
      coversTop := hX
      presentation := fun i ↦ (h i).choose }
  have hq : q.IsFinitePresentation := ⟨fun i ↦ (h i).choose_spec⟩
  exact ⟨q.shrink, inferInstance⟩

end Locality

/-! ### An invertible sheaf of modules is of finite presentation -/

section Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **An invertible sheaf of modules is of finite presentation.**

This is the step of Tag 0B8M's converse that Stacks attributes to Tag 0B8K. By Tag 0B8N (b)
every object of the site has a covering family on whose members `L` is a split subobject of a
finite product of copies of the structure sheaf, hence has a finite presentation there; the union
over all objects of those families covers the terminal object, and finite presentation is
local.

This is also the finite-presentation half of Tag 0B8N (a). -/
@[stacks 0B8N "(a), the finite-presentation half"]
theorem isFinitePresentation_of_isInvertible
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (hL :
      IsInvertible O hO L) :
    L.IsFinitePresentation := by
  have := hL
  choose Idx V f hJ hsplit using fun U : C ↦ exists_cover_isDirectSummand_finiteFree hO L U
  refine isFinitePresentation_of_coversTop (fun p : Σ U : C, Idx U ↦ V p.1 p.2) ?_ ?_
  · intro U
    refine J.superset_covering (le_trans (Sieve.ofArrows_le_ofObjects (V U) (f U))
      (Sieve.ofObjects_mono ?_)) (hJ U)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨U, i⟩, rfl⟩
  · rintro ⟨U, i⟩
    obtain ⟨n, s, hs⟩ := hsplit U i
    have := hs
    exact exists_isFinite_presentation_of_isSplitMono_pi s

end Invertible

/-! ### The two stalks of the structure sheaf of a ringed space -/

section RingedSpaceStalk

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace TopologicalSpace

variable (X : RingedSpace.{u, u})

/-- The comparison of the two stalks of the structure sheaf, in the vocabulary of Tag 01CB: it
matches the ring germ maps. This is `SemilinearStalk.commStalkRingEquiv_germ` with the structure
sheaf of a ringed space written as `Stacks.SheafOfModules.TensorStalkRingedSpace.O`. -/
lemma commStalkRingEquiv_ringGerm (x : X.carrier) (U : Opens X.carrier) (hxU : x ∈ U)
    (a : (O X).obj (op U)) :
    SemilinearStalk.commStalkRingEquiv X.presheaf x
        (TopCat.Presheaf.germ (O X) U x hxU a) = ringGerm X x U hxU a :=
  SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hxU a

/-- **The two scalar actions on the stalk of a sheaf of modules agree.** The action of the
`RingCat`-stalk of the structure sheaf is the action of the `CommRingCat`-stalk, transported
along `SemilinearStalk.commStalkRingEquiv`. Both are pinned down by the germ formula
`germ (r • m) = germ r • germ m`, and every element of a stalk is a germ. -/
lemma ringStalk_smul_eq (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (r : ToType (TopCat.Presheaf.stalk (O X) x)) (m : grpStalk X F x) :
    r • m = SemilinearStalk.commStalkRingEquiv X.presheaf x r • m := by
  obtain ⟨W, hxW, α, hα⟩ :=
    X.presheaf.exists_germ_eq (SemilinearStalk.commStalkRingEquiv X.presheaf x r)
  obtain ⟨V, hxV, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) F.presheaf m
  set U : Opens X.carrier := W ⊓ V with hUdef
  have hxU : x ∈ U := ⟨hxW, hxV⟩
  set α' : X.presheaf.obj (op U) := (X.presheaf.map (homOfLE inf_le_left : U ⟶ W).op).hom α
    with hα'
  set t' : F.obj (op U) := (F.map (homOfLE inf_le_right : U ⟶ V).op).hom t with ht'
  have hr : r = TopCat.Presheaf.germ (O X) U x hxU α' := by
    refine (SemilinearStalk.commStalkRingEquiv X.presheaf x).injective ?_
    rw [commStalkRingEquiv_ringGerm, hα', ← hα]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x hxU α).symm
  have hm : m = grpGerm X F x U hxU t' := by
    rw [ht', ← ht]
    exact (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) F.presheaf
      (homOfLE inf_le_right) x hxU t).symm
  rw [hr, hm, commStalkRingEquiv_ringGerm,
    ← Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X F x U hxU α' t']
  exact (PresheafOfModules.germ_ringCat_smul F x U hxU α' t').symm

/-- **The hypothesis of Tag 0B8J from the conclusion of Tag 0AFW.** A stalk of a sheaf of modules
which is free of rank one over the `CommRingCat`-stalk of the structure sheaf is free of rank one
over the `RingCat`-stalk, which is the ring in which Tag 0B8J phrases its hypothesis. -/
theorem nonempty_stalk_linearEquiv_finsupp (F : PresheafOfModules.{u} (O X)) (x : X.carrier)
    (h : Nonempty (grpStalk X F x ≃ₗ[ringStalk X x] ringStalk X x)) :
    Nonempty (ToType (TopCat.Presheaf.stalk F.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (O X) x)]
        (ULift.{u} (Fin 1) →₀ ToType (TopCat.Presheaf.stalk (O X) x))) := by
  obtain ⟨e⟩ := h
  refine ⟨AddEquiv.toLinearEquiv
    (e.toAddEquiv.trans (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toAddEquiv)
      (fun c m ↦ ?_) ≪≫ₗ
      (LinearEquiv.funUnique (ULift.{u} (Fin 1)) _ _).symm ≪≫ₗ
      (Finsupp.linearEquivFunOnFinite _ _ (ULift.{u} (Fin 1))).symm⟩
  have hsmul : e (c • m) = SemilinearStalk.commStalkRingEquiv X.presheaf x c * e m := by
    rw [ringStalk_smul_eq X F x c m, e.map_smul]
    rfl
  change (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm (e (c • m))
    = c * (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm (e m)
  rw [hsmul, map_mul, RingEquiv.symm_apply_apply]

end RingedSpaceStalk

/-! ### Tag 0B8M -/

section Converse

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace TopologicalSpace

variable (X : RingedSpace.{u, u}) (L : SheafOfModules.{u} (structureSheafRing X))

/-- An invertible sheaf of modules on a ringed space is of finite presentation. -/
theorem isFinitePresentation_of_isInvertible_ringedSpace
    (hL : IsInvertible X.presheaf (structureSheafRing X).property L) :
    L.IsFinitePresentation :=
  isFinitePresentation_of_isInvertible (structureSheafRing X).property L hL

end Converse

end Stacks.SheafOfModules

end
