module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Module.Projective.Determinant.AnnihilatorIdempotent

/-!
# The degreewise exterior annihilator vanishes outside a finite cover of the rank strata

Let `F` be a sheaf of modules on a topological space `X` whose stalks are finite projective
modules over the stalks of the structure sheaf, and let `det(F) = ∐ₙ annₙ(F)` be the determinant
of [Stacks, Tag 0FJN], the degreewise annihilator of the degree-one part of the exterior algebra.
This file proves that `annₙ(F)` is a zero object for all but finitely many `n`.

The bound is *not* a bound on a rank: a flat sheaf of modules of finite presentation on a ringed
space is not locally of constant rank, and the constant-rank route is refuted — see the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorDeterminantInvertible.lean`. What takes its
place is the finite cover of the prime spectrum by the clopen rank strata of a finite projective
module, `ProjectiveDeterminant.exists_finset_rankLocus_cover`. The degrees that survive are the
members of such a finset, and the hypothesis below is exactly the one
`ProjectiveDeterminant.rankIdempotent_eq_zero_of_not_mem_finset_cover` consumes, imposed on
every stalk at once.

## Main results

* `Stacks.ExteriorAnnihilator.part_eq_bot_of_rankIdempotent_eq_zero`: the degree-`n` part of the
  annihilator of the degree-one elements of `⋀_R M` vanishes as soon as the rank-`n` idempotent
  of the finite projective module `M` does.
* `Stacks.ExteriorAnnihilator.part_eq_bot_of_not_mem_finset_cover`: consequently it vanishes for
  every degree outside a finset whose rank strata cover `Spec R`.
* `Stacks.SheafOfModules.terminalSection_val_eq_zero`: a vanishing section over a terminal object
  restricts to the vanishing compatible family.

In the namespace `SheafOfModules.TensorExteriorSymmetricAlgebras`:

* `isZero_exteriorAnnihilator_of_part_eq_bot`: **a degreewise exterior annihilator all of whose
  stalkwise parts vanish is a zero object.**
* `isZero_exteriorAnnihilator_of_rankIdempotent_eq_zero`: **`annₙ(F) = 0` when the rank-`n`
  idempotent of every stalk vanishes**, which is what the base change of the rank idempotent
  produces on a trivialising open.
* `isZero_exteriorAnnihilator_of_not_mem_finset_cover`: **`annₙ(F) = 0` for `n` outside a finset
  covering the rank strata of every stalk**, the form the local description of `det(F)` consumes.
* `isZero_exteriorAnnihilator_of_isFlat_of_not_mem_finset_cover`: the same on a ringed space, with
  the stalkwise finiteness and projectivity replaced by the hypotheses of Tag 0FJN — finite
  presentation of `F` and flatness of its stalks.

## Implementation notes

**Why the argument is stalkwise.** A section of `⋀ⁿ F` annihilated by every degree-one section
need not visibly vanish on the open it is given on, so there is no sectionwise argument; and the
sections of `⋀ⁿ F` over `U` are not the exterior power of the sections of `F` over `U`, since
`⋀ⁿ F` is a sheafification. The stalk of `annₙ(F)` is computed by
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAnnihilatorStalkEquiv`, but only the
easy half of that computation is used here — the germ of an annihilated section is annihilated in
the exterior algebra of the stalk — so no finite-presentation hypothesis is needed for the
general statement and the proof mirrors
`SheafOfModules.TensorExteriorSymmetricAlgebras.isZero_exteriorAnnihilator`, the constant-rank
case, with the vanishing of the stalkwise part taken as a hypothesis rather than read off a
basis.

**What this file adds over the sections route, which is also available.** The vanishing can
instead be read off multiplication by the idempotent as an endomorphism of the identity functor,
`Stacks.SheafOfModules.globalSectionToEnd`: a compatible family of local scalars which acts as
the identity on a submodule and vanishes makes that submodule a zero object, which is
`Stacks.SheafOfModules.isZero_toSheafOfModules_of_smul_eq_self`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SubmoduleIdempotentRetract.lean`). That route
works on an arbitrary site, in particular on a slice site where there are no stalks, but it
consumes the hypothesis that the idempotent acts as the identity on `annₙ` *on sections* — which
is a form of the local description of the annihilator.

The statements here consume no such hypothesis: only that the stalks of `F` are finite
projective. So the two discharge the vanishing from independent inputs, and neither subsumes the
other — this one needs stalks and so is restricted to the site of opens of a space, that one
needs the sectionwise identity and so is restricted to where the local description is already
in hand. `Stacks.SheafOfModules.terminalSection_val_eq_zero` below is the last step of the
sections route: the compatible family obtained from a vanishing global scalar vanishes.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf

universe u v w

namespace Stacks.ExteriorAnnihilator

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The degreewise annihilator vanishes where the rank idempotent does.** The rank-`n`
idempotent acts as the identity on the degree-`n` annihilator
(`ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart`), so if it is zero
then so is every element of that annihilator. -/
theorem part_eq_bot_of_rankIdempotent_eq_zero [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (he : ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n = 0) :
    part R M n = ⊥ := by
  refine le_antisymm (fun y hy => ?_) bot_le
  have hself := ProjectiveDeterminant.rankIdempotent_smul_eq_self_of_mem_annihilatorPart
    (R := R) (M := M) (y := y) hy
  rw [he, zero_smul] at hself
  exact (Submodule.mem_bot _).2 (Subtype.ext hself.symm)

/-- **The degreewise annihilator vanishes outside a finite cover of the rank strata.** Outside
such a finset the rank stratum is empty, so its cutting idempotent is zero by
`ProjectiveDeterminant.rankIdempotent_eq_zero_of_not_mem_finset_cover`. -/
theorem part_eq_bot_of_not_mem_finset_cover [Module.Finite R M] [Module.Projective R M]
    {s : Finset ℕ}
    (hs : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ m ∈ s, ProjectiveDeterminant.rankLocus (R := R) M m)
    {n : ℕ} (hn : n ∉ s) : part R M n = ⊥ :=
  part_eq_bot_of_rankIdempotent_eq_zero n
    (ProjectiveDeterminant.rankIdempotent_eq_zero_of_not_mem_finset_cover hs hn)

end Stacks.ExteriorAnnihilator

namespace Stacks.SheafOfModules

open scoped IsMulCommutative

/-- **The compatible family of local scalars restricted from a vanishing global scalar
vanishes.** With `Stacks.SheafOfModules.isZero_toSheafOfModules_of_smul_eq_self` this is the last
step of the sections route to the vanishing of the degreewise annihilator: on a site with a
terminal object the rank idempotents are sections over it, and outside a finite cover of the
rank strata they are zero. -/
theorem terminalSection_val_eq_zero {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)] (T : C)
    (hT : IsTerminal T) {f : R.obj.obj (op T)} (hf : f = 0) (U : Cᵒᵖ) :
    (terminalSection R T hT f).val U = 0 := by
  change R.obj.map (hT.from U.unop).op f = 0
  rw [hf]
  exact map_zero (R.obj.map (hT.from U.unop).op).hom

end Stacks.SheafOfModules

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)

/-- **Every germ of the degree-`n` exterior annihilator vanishes when the degree-`n` part of the
annihilator in the stalk does.** The germ of an annihilated section is annihilated in the
exterior algebra of the stalk, hence lies in that part. -/
theorem subsingleton_stalk_exteriorAnnihilator_of_part_eq_bot (x : ↥X) (n : ℕ)
    (hbot : Stacks.ExteriorAnnihilator.part (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) n = ⊥) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
      (A.exteriorAnnihilator n).toSheafOfModules.val.presheaf x)) := by
  refine subsingleton_of_forall_eq 0 fun a => ?_
  refine injective_submoduleStalkι x ?_
  rw [map_zero]
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (A.exteriorAnnihilator n).toSheafOfModules.val.presheaf a
  rw [submoduleStalkι_germ x U hx s]
  refine A.germ_eq_zero_of_germWedge_eq_zero x n hx _ ?_
  exact congrArg Subtype.val ((Submodule.mem_bot _).1 (hbot.le
    ((Stacks.ExteriorAnnihilator.mem_part_iff _).mpr fun μ =>
      A.mul_germWedge_eq_zero_of_isExteriorAnnihilated x n hx _ (Subtype.property s) μ)))

/-- **A degreewise exterior annihilator all of whose stalkwise parts vanish is a zero object.**
All its stalks are singletons, so its identity is the zero morphism. -/
theorem isZero_exteriorAnnihilator_of_part_eq_bot (n : ℕ)
    (hbot : ∀ x : ↥X, Stacks.ExteriorAnnihilator.part
      (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) n = ⊥) :
    IsZero ((A.exteriorAnnihilator n).toSheafOfModules) :=
  (IsZero.iff_id_eq_zero _).2
    (Stacks.SheafOfModules.TopWedge.id_eq_zero_of_subsingleton_stalk _
      fun y => A.subsingleton_stalk_exteriorAnnihilator_of_part_eq_bot y n (hbot y))

/-- **The degree-`n` exterior annihilator vanishes where the rank-`n` idempotent of every stalk
does.** This is the form the base change of the rank idempotent produces: on a trivialising open
the stalk of `F` is a base change of the module of sections, and
`ProjectiveDeterminant.rankIdempotent_baseChange` carries the vanishing of the idempotent of the
module of sections to the vanishing of the idempotent of every stalk. -/
theorem isZero_exteriorAnnihilator_of_rankIdempotent_eq_zero (n : ℕ)
    (hfin : ∀ x : ↥X, Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)))
    (hproj : ∀ x : ↥X, Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)))
    (he : ∀ x : ↥X, @ProjectiveDeterminant.rankIdempotent
      (ToType (TopCat.Presheaf.stalk Osharp.obj x)) _
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) _ _ (hfin x) (hproj x) n = 0) :
    IsZero ((A.exteriorAnnihilator n).toSheafOfModules) := by
  have := hfin
  have := hproj
  exact A.isZero_exteriorAnnihilator_of_part_eq_bot n fun x =>
    Stacks.ExteriorAnnihilator.part_eq_bot_of_rankIdempotent_eq_zero n (he x)

/-- **The degree-`n` exterior annihilator vanishes for `n` outside a finset covering the rank
strata of every stalk.**

The hypotheses are exactly those of
`ProjectiveDeterminant.rankIdempotent_eq_zero_of_not_mem_finset_cover`, imposed on every stalk
with one finset `s` serving for all of them: the stalk of `F` at `x` is a finite projective
module over the stalk of the structure sheaf, and the rank strata of that module indexed by `s`
cover `Spec` of that stalk. For `n ∉ s` the rank-`n` idempotent of each stalk vanishes, hence so
does the degree-`n` part of the annihilator in each stalk, hence so does `annₙ(F)`.

Note that the conclusion is stated for every `n ∉ s`, which is weaker as a hypothesis than any
inequality `n > N`: a degree exceeding every member of `s` is in particular not a member. -/
theorem isZero_exteriorAnnihilator_of_not_mem_finset_cover
    (hfin : ∀ x : ↥X, Module.Finite (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)))
    (hproj : ∀ x : ↥X, Module.Projective (ToType (TopCat.Presheaf.stalk Osharp.obj x))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)))
    {s : Finset ℕ}
    (hs : ∀ x : ↥X, (Set.univ : Set (PrimeSpectrum
        (ToType (TopCat.Presheaf.stalk Osharp.obj x)))) ⊆
      ⋃ m ∈ s, ProjectiveDeterminant.rankLocus
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) m)
    {n : ℕ} (hn : n ∉ s) :
    IsZero ((A.exteriorAnnihilator n).toSheafOfModules) := by
  have := hfin
  have := hproj
  exact A.isZero_exteriorAnnihilator_of_part_eq_bot n fun x =>
    Stacks.ExteriorAnnihilator.part_eq_bot_of_not_mem_finset_cover (hs x) hn

/-! ### The form the determinant lemma on a ringed space consumes -/

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **The degree-`n` exterior annihilator vanishes for `n` outside a finset covering the rank
strata of every stalk**, on a ringed space and under the hypotheses of Tag 0FJN themselves: the
stalkwise finiteness and projectivity are supplied by the finite presentation of `G` together
with flatness of its stalks, through
`SheafOfModules.TensorExteriorSymmetricAlgebras.projective_stalk` and
`Stacks.SheafOfModules.finitePresentation_stalk`. -/
theorem isZero_exteriorAnnihilator_of_isFlat_of_not_mem_finset_cover {Y : RingedSpace.{u, u}}
    (G : SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation]
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) G)
    (hflat : ∀ x : Y, @Module.Flat _ _ _ _ (Stacks.SheafOfModules.stalkModule G x))
    {s : Finset ℕ}
    (hs : ∀ x : Y, (Set.univ : Set (PrimeSpectrum _)) ⊆
      ⋃ m ∈ s, @ProjectiveDeterminant.rankLocus _ _ _ _
        (Stacks.SheafOfModules.stalkModule G x) m)
    {n : ℕ} (hn : n ∉ s) :
    IsZero ((A.exteriorAnnihilator n).toSheafOfModules) := by
  let : SheafOfModules.IsFinitePresentation
      (R := toRingCat (Opens.grothendieckTopology Y.carrier) Y.sheaf) G := ‹_›
  refine A.isZero_exteriorAnnihilator_of_not_mem_finset_cover (fun x => ?_)
    (fun x => projective_stalk x (hflat x)) hs hn
  let instG := Stacks.SheafOfModules.stalkModule G x
  have : @Module.FinitePresentation _ _ _ _ instG :=
    Stacks.SheafOfModules.finitePresentation_stalk G x
  infer_instance

end RingedSpace

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
