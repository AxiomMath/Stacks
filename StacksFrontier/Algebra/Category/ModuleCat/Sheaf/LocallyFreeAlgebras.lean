module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor, exterior and symmetric algebras of a locally free sheaf of modules are locally free

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `F` a locally free sheaf of
modules over the underlying sheaf of rings. This file proves clause (2) of Stacks Tag 01CL: the
sheaves of modules underlying `T(F)`, `⋀(F)` and `Sym(F)` are again locally free.

## Where the content is

Tag 01CL's proof opens by warning that an infinite direct sum of locally free sheaves of modules
need *not* be locally free: the opens on which the summands trivialise may intersect in no
neighbourhood of a point. What rescues the lemma is that a **single** member of the trivialising
covering of `F` trivialises `Tⁿ(F)`, `⋀ⁿ(F)` and `Symⁿ(F)` for every `n` at once. That is
established inside the proof of clause (6) of Tag 01CK and is recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers` as
`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree`,
`symmetricPowerOverFreeIsoOfIsoFree` and `exists_nonempty_iso_free_tensorPowerOver`, each of
which takes one object `U` of the site and one trivialisation of `F|_U` and returns a
trivialisation of the degree-`n` power over that same `U`, for every `n` and with no further
shrinking. So the uniformity is not a hypothesis here; it is the input those three supply.

Once it is in hand, all that remains of the tag is to recognise a coproduct of free sheaves of
modules as a free sheaf of modules, which is `SheafOfModules.nonempty_iso_free_coprod`, and to
move the coproduct past the restriction to the slice site, which is
`SheafOfModules.overSigmaIso`. The source's closing "The lemma follows" is
`Stacks.SheafOfModules.isLocallyFree_coprod_of_small` below.

## Main results

* `Stacks.SheafOfModules.isLocallyFree_coprod_of_small`: **a coproduct of sheaves of modules all
  of which are free over one and the same covering family of the terminal object is locally
  free**, for an index type that is only `Small.{u}` — which is what makes it applicable to an
  `ℕ`-graded coproduct at a nonzero module universe.
* `Stacks.SheafOfModules.isLocallyFree_tensorAlgebraSheaf_of_isLocallyFree`,
  `isLocallyFree_exteriorAlgebraSheaf_of_isLocallyFree` and
  `isLocallyFree_symmetricAlgebraSheaf_of_isLocallyFree`: **clause (2) of Tag 01CL**, for the
  three algebras.

## Implementation notes

**Why the index type has to be shrunk.** `SheafOfModules.free` takes an index in the module
universe `u`, so `SheafOfModules.nonempty_iso_free_coprod` is stated for a `Type u`-indexed
coproduct; a graded algebra sheaf is indexed by `ℕ : Type 0`, and instantiating a `Type u`
statement at `ℕ` would force `u = 0`. The reindexing along `equivShrink` is
`SheafOfModules.sigmaShrinkIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod`, where the same
obstruction is resolved the same way for quasi-coherence.

**The products hypothesis, and why it is not a narrowing.** `HasBinaryProducts C` enters through
`SheafOfModules.overSigmaIso`, i.e. through the only route in Mathlib to the fact that
restriction to a slice site preserves coproducts: the right adjoint of `Over.forget Y` is
`Over.star Y`. Stacks assumes no products of a site, but the statement of the tag is about a
ringed space, where the site is `TopologicalSpace.Opens` and binary products are intersections
of opens, so nothing the tag asserts is lost.

**The index types of the summands are not named.** For the two quotients they are the degree-`n`
multidegrees in and the `n`-element subsets of the local index type; for the tensor powers they
are left under an `∃`, for the reason recorded at
`Stacks.SheafOfModules.exists_nonempty_iso_free_tensorPower`. Clause (2) asserts only local
freeness, so all three are passed as an opaque family `K : I → ι → Type u` and chosen by
`choose` where a tensor power is involved.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u₁ u

namespace Stacks.SheafOfModules

/-! ### A coproduct that is free over one common covering family -/

section Coprod

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]

/-- **A coproduct of sheaves of modules all of which are free over one and the same covering
family of the terminal object is locally free.** This is the formal step the uniformity of the
trivialising neighbourhood feeds, and it is the closing step of Stacks Tag 01CL: over `X i` the
restriction of `∐ P` is the coproduct of the restrictions
(`SheafOfModules.overSigmaIso`), and a coproduct of free sheaves of modules is free on the sigma
type of the index types (`SheafOfModules.nonempty_iso_free_coprod`).

Per-summand local freeness would *not* suffice, which is why the covering family is shared: the
opens on which the summands trivialise may intersect in no neighbourhood of a point. -/
theorem isLocallyFree_coprod_of_small {ι : Type w} [Small.{u} ι]
    {P : ι → _root_.SheafOfModules.{u} R} [HasCoproduct P] {I : Type u₁}
    (X : I → C) (hX : J.CoversTop X) (K : I → ι → Type u)
    (E : ∀ (i : I) (n : ι), Nonempty ((P n).over (X i) ≅
      _root_.SheafOfModules.free (R := R.over (X i)) (K i n))) :
    (∐ P).IsLocallyFree := by
  have H : ∀ i : I, ∃ D : Type u, Nonempty ((∐ P).over (X i) ≅
      _root_.SheafOfModules.free (R := R.over (X i)) D) := fun i => by
    obtain ⟨e⟩ := _root_.SheafOfModules.nonempty_iso_free_coprod
      (O := R.over (X i))
      (P := fun j : Shrink.{u} ι => (P ((equivShrink ι).symm j)).over (X i))
      (fun j => K i ((equivShrink ι).symm j))
      (fun j => E i ((equivShrink ι).symm j))
    exact ⟨_, ⟨(_root_.SheafOfModules.overFunctor R (X i)).mapIso
        (_root_.SheafOfModules.sigmaShrinkIso (P := P)).symm ≪≫
      (_root_.SheafOfModules.overSigmaIso
        (fun j : Shrink.{u} ι => P ((equivShrink ι).symm j)) (X i)).symm ≪≫ e⟩⟩
  choose D hD using H
  exact isLocallyFree_of_forall_iso_free X hX D fun i => (hD i).some

end Coprod

/-! ### Clause (2) of Tag 01CL -/

section Conclusions

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)} [hF : F.IsLocallyFree]
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)

/-- **The symmetric algebra of a locally free sheaf of modules is locally free.** The covering
family is the one that trivialises `F`; no degree needs a smaller object of the site, because
`Stacks.SheafOfModules.symmetricPowerOverFreeIsoOfIsoFree` trivialises every degree over that
same object. -/
@[stacks 01CL "the symmetric algebra of a locally free module sheaf is locally free",
  sga "3 XXII 5.3.0" "partial"]
theorem isLocallyFree_symmetricAlgebraSheaf_of_isLocallyFree :
    A.symmetricAlgebraSheaf.IsLocallyFree := by
  classical
  obtain ⟨q, hq⟩ := hF.exists_isLocallyFreeData
  refine isLocallyFree_coprod_of_small q.X q.coversTop
    (fun i n => {d : (q.generators i).I →₀ ℕ | d.degree = n}) fun i n => ?_
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨symmetricPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
    (asIso (q.generators i).π).symm⟩

/-- **The exterior algebra of a locally free sheaf of modules is locally free.** The covering
family is the one that trivialises `F`, and
`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree` trivialises every degree over the same
object of the site. -/
@[stacks 01CL "the exterior algebra of a locally free module sheaf is locally free"]
theorem isLocallyFree_exteriorAlgebraSheaf_of_isLocallyFree :
    A.exteriorAlgebraSheaf.IsLocallyFree := by
  classical
  obtain ⟨q, hq⟩ := hF.exists_isLocallyFreeData
  refine isLocallyFree_coprod_of_small q.X q.coversTop
    (fun i n => Set.powersetCard ((q.generators i).I) n) fun i n => ?_
  have : IsIso (q.generators i).π := hq.isIso i
  let _ : LinearOrder ((q.generators i).I) := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨exteriorPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
    (asIso (q.generators i).π).symm⟩

/-- **The tensor algebra of a locally free sheaf of modules is locally free.** The covering
family is the one that trivialises `F`, and
`Stacks.SheafOfModules.exists_nonempty_iso_free_tensorPowerOver` trivialises every degree over
the same object of the site. -/
@[stacks 01CL "the tensor algebra of a locally free module sheaf is locally free"]
theorem isLocallyFree_tensorAlgebraSheaf_of_isLocallyFree :
    A.tensorAlgebraSheaf.IsLocallyFree := by
  obtain ⟨q, hq⟩ := hF.exists_isLocallyFreeData
  have H : ∀ (i : q.I) (n : ℕ), ∃ K : Type u,
      Nonempty ((A.tensor.piece (n : ℤ)).over (q.X i) ≅
        _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over (q.X i)) K) := by
    intro i n
    have : IsIso (q.generators i).π := hq.isIso i
    exact exists_nonempty_iso_free_tensorPowerOver A (q.X i) n ((q.generators i).I)
      (asIso (q.generators i).π).symm
  choose K hK using H
  exact isLocallyFree_coprod_of_small q.X q.coversTop K hK

end Conclusions

end Stacks.SheafOfModules

end
