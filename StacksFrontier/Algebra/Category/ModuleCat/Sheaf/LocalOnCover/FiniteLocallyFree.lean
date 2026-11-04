module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of a sheaf of modules is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the clause for finite local
freeness: a sheaf of modules on a ringed site is finite locally free exactly when its
restrictions to the members of some covering family are finite locally free on the localized
ringed sites, and exactly when those restrictions can be taken finite free.

Both equivalences reduce to comparing two readings of one module.  For `V` an object of the
slice site over `U`, the module `(M.over U).over V` on the iterated slice and the module
`M.over V.left` on the slice over the base object `V.left` are carried to one another by
`Over.iteratedSliceEquiv V`, and a finite free cofan is carried with them:
`isColimitCofanTransport` transports a cofan of copies of the structure sheaf along any
equivalence of categories of sheaves of modules that matches up the two structure sheaves.  The
descent step itself — that finite freeness on a family covering the final object gives finite
local freeness everywhere — is
`Stacks.SheafOfModules.exists_cover_isColimitCofan_of_coversTop`.

## Main results

* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite`:
  finite local freeness is equivalent to finite local freeness of the restrictions to the
  members of some covering family.  This is the equivalence of conditions (a) and (b) of
  Stacks 03DN for finite local freeness.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree`: finite local
  freeness is equivalent to finite freeness of those restrictions.  This is the equivalence of
  conditions (a) and (c).
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree`: finite local
  freeness in the local-generators form of Stacks 01C6(2) implies finite local freeness in the
  covering-family form of Stacks 03DL(2).

## Implementation notes

Finite local freeness is `SheafOfModules.IsFiniteLocallyFreeOnSite`, which is Stacks 03DL(2),
and the localized ringed site is `AlgebraicGeometry.RingedSite.over`, which is Stacks 04IX; no
notion is introduced here.  Rank zero is included, as in the source.

The comparison with Stacks 01C6(2), `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, is
a consequence of the same descent step and is proved here because that is where the step lives.
Local generators data is already a family covering the final object, so only its members have to
be recognized as finite free: a finite family of generating sections whose associated morphism
out of the free sheaf is invertible is a colimiting cofan of copies of the structure sheaf, after
reindexing its finite index type by `Fin n` with
`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`.  The converse implication is not proved: it
would have to manufacture generating sections over a covering of the final object out of the
covering families of Stacks 03DL(2), which is a construction and not a transport.

The comparison `sliceEquiv` of the iterated slice with the slice over the base object, the two
objectwise-identity isomorphisms identifying the two readings of a module and of the structure
sheaf, and the cofan transport along an equivalence are all in
`StacksDraft.Ch18.Sec23.RestrictionPreservesColimits`, since the companion statements for local
generation need exactly the same comparison.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w u₁ v₁ u₂ v₂

/-- Finite freeness of the restriction of `M` to `V.left` gives finite freeness of its
restriction to the iterated slice over `V`. -/
public theorem exists_isColimitCofan_overOver {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (U : C)
    (V : Over U)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (R.over V.left) ⟶ M.over V.left,
      Nonempty (IsColimit (Cofan.mk (M.over V.left) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((R.over U).over V) ⟶ (M.over U).over V,
      Nonempty (IsColimit (Cofan.mk ((M.over U).over V) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  exact ⟨n, _, ⟨isColimitCofanTransport (sliceEquiv R U V) (sliceEquivUnitIso R U V)
    (sliceEquivObjIso M U V) ι hc⟩⟩

/-- Finite freeness of the restriction of `M` to the iterated slice over `V` gives finite
freeness of its restriction to `V.left`. -/
private theorem exists_isColimitCofan_overOver_symm {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) (U : C)
    (V : Over U)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit ((R.over U).over V) ⟶ (M.over U).over V,
      Nonempty (IsColimit (Cofan.mk ((M.over U).over V) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
      SheafOfModules.unit (R.over V.left) ⟶ M.over V.left,
      Nonempty (IsColimit (Cofan.mk (M.over V.left) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  let e := sliceEquiv R U V
  let η : e.symm.functor.obj (SheafOfModules.unit ((R.over U).over V)) ≅
      SheafOfModules.unit (R.over V.left) :=
    e.inverse.mapIso (sliceEquivUnitIso R U V).symm ≪≫
      (e.unitIso.app (SheafOfModules.unit (R.over V.left))).symm
  let ρ : e.symm.functor.obj ((M.over U).over V) ≅ M.over V.left :=
    e.inverse.mapIso (sliceEquivObjIso M U V).symm ≪≫ (e.unitIso.app (M.over V.left)).symm
  exact ⟨n, _, ⟨isColimitCofanTransport e.symm η ρ ι hc⟩⟩

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **Stacks 03DN, finite local freeness.** A sheaf of modules on a ringed site is finite
locally free if and only if its restriction to each member of some covering family of the final
object is finite locally free on the corresponding localized ringed site. -/
@[stacks 03DN "finite_locally_free"]
theorem isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite :
    SheafOfModules.IsFiniteLocallyFreeOnSite F ↔
      ∃ (I : Type (max u v)) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsFiniteLocallyFreeOnSite
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (U i)).O)) (F.over (U i)) := by
  constructor
  · intro hF
    rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit] at hF
    classical
    let I₀ := ULift.{max u v} X.C
    let U₀ : I₀ → X.C := fun i => i.down
    refine ⟨I₀, U₀, coversTop_ulift_self X.J, ?_⟩
    intro i
    apply (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit _).mpr
    intro W
    obtain ⟨I, V, f, hcov, hfree⟩ := hF W.left
    refine ⟨I, (fun j => Over.mk (f j ≫ W.hom)),
      (fun j => Over.homMk (f j) (by simp)), ?_, ?_⟩
    · show Sieve.ofArrows (fun j => Over.mk (f j ≫ W.hom))
        (fun j => Over.homMk (f j) (by simp)) ∈ (X.J.over (U₀ i)) W
      rw [GrothendieckTopology.mem_over_iff]
      simpa [Sieve.overEquiv, Sieve.functorPushforward_ofArrows] using hcov
    · intro j
      exact exists_isColimitCofan_overOver F (U₀ i) (Over.mk (f j ≫ W.hom)) (hfree j)
  · rintro ⟨I, U, hU, hlocal⟩
    classical
    have hlocal' := fun i =>
      (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit _).mp (hlocal i)
    choose I' V f hcov hfree using fun i : I => hlocal' i (Over.mk (𝟙 (U i)))
    have hcovBase : ∀ i, Sieve.ofArrows (fun j => (V i j).left)
        (fun j => (V i j).hom) ∈ X.J (U i) := by
      intro i
      have hci : Sieve.ofArrows (V i) (f i) ∈
          (X.J.over (U i)) (Over.mk (𝟙 (U i))) := hcov i
      have h := (GrothendieckTopology.mem_over_iff (J := X.J)
        (S := Sieve.ofArrows (V i) (f i))).mp hci
      have heq : ∀ j, (f i j).left = (V i j).hom :=
        fun j => by simpa using (Over.w (f i j))
      simpa [Sieve.overEquiv, Sieve.functorPushforward_ofArrows, heq] using h
    have hslice : ∀ i, (X.J.over (U i)).CoversTop (V i) := fun i =>
      coversTop_over_of_ofArrows_mem X.J (U i) (fun j => (V i j).left)
        (fun j => (V i j).hom) (hcovBase i)
    have hW : X.J.CoversTop (fun ij : (Σ i, I' i) => (V ij.1 ij.2).left) := hU.over hslice
    refine (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit F).mpr
      (fun W => exists_cover_isColimitCofan_of_coversTop _ hW F (fun ij => ?_) W)
    exact exists_isColimitCofan_overOver_symm F (U ij.1) (V ij.1 ij.2) (hfree ij.1 ij.2)

/-- **Stacks 03DN, finite local freeness.** A sheaf of modules on a ringed site is finite
locally free if and only if its restriction to each member of some covering family of the final
object is finite free. -/
@[stacks 03DN "finite_locally_free"]
theorem isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree :
    SheafOfModules.IsFiniteLocallyFreeOnSite F ↔
      ∃ (I : Type (max u v)) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, ∃ n : ℕ,
          ∃ (ι : ∀ _ : Fin n,
            SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (U i)) ⟶
              F.over (U i)),
            Nonempty (IsColimit (Cofan.mk (F.over (U i)) ι)) := by
  constructor
  · intro hF
    rw [SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit] at hF
    classical
    let I₀ := ULift.{max u v} X.C
    let U₀ : I₀ → X.C := fun i => i.down
    choose I V f hcov hfree using fun i : I₀ => hF i.down
    have hslice : ∀ i : I₀,
        (X.J.over (U₀ i)).CoversTop (fun j => Over.mk (f i j)) := fun i =>
      coversTop_over_of_ofArrows_mem X.J (U₀ i) (V i) (f i) (hcov i)
    exact ⟨(Σ i, I i), fun ij => (V ij.1 ij.2), (coversTop_ulift_self X.J).over hslice,
      fun ij => hfree ij.1 ij.2⟩
  · rintro ⟨I, U, hU, hfree⟩
    exact (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit F).mpr
      (fun W => exists_cover_isColimitCofan_of_coversTop U hU F hfree W)

/-! ### Comparison with the local-generators form of Stacks 01C6(2) -/

section LocalGenerators

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite family of generating sections of a sheaf of modules whose associated morphism out
of the free sheaf is invertible exhibits that module as a coproduct of finitely many copies of
the structure sheaf. -/
private theorem exists_isColimitCofan_of_isIso_generators (M : SheafOfModules.{w} R) (Y : C)
    (σ : (M.over Y).GeneratingSections) (hiso : IsIso σ.π) (hfin : Finite σ.I) :
    ∃ (n : ℕ) (ι : Fin n → (SheafOfModules.unit (R.over Y) ⟶ M.over Y)),
      Nonempty (IsColimit (Cofan.mk (M.over Y) ι)) := by
  classical
  have hc : IsColimit (Cofan.mk (M.over Y)
      (fun j : σ.I => SheafOfModules.ιFree j ≫ σ.π)) :=
    IsColimit.ofIsoColimit (SheafOfModules.isColimitFreeCofan σ.I)
      (Cocone.ext (@asIso _ _ _ _ _ hiso) (by rintro ⟨j⟩; rfl))
  exact ⟨Nat.card σ.I, fun j => SheafOfModules.ιFree ((Finite.equivFin σ.I).symm j) ≫ σ.π,
    ⟨Cofan.isColimitEquivOfEquiv (Finite.equivFin σ.I).symm
      (Cofan.mk (M.over Y) (fun j : σ.I => SheafOfModules.ιFree j ≫ σ.π)) hc⟩⟩

/-- **The local-generators form of Stacks 01C6(2) implies the covering-family form of
Stacks 03DL(2).** A sheaf of modules carrying local generators data which is a finite local
free basis is finite locally free on the site.

The data is already a family covering the final object, and on each member the generating
sections exhibit the module as a coproduct of finitely many copies of the structure sheaf; the
descent step `Stacks.SheafOfModules.exists_cover_isColimitCofan_of_coversTop` then produces a
covering family with that property over every object of the site. -/
theorem isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree (M : SheafOfModules.{w} R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{w, v, u} M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  obtain ⟨q, hqfree, hqfin⟩ := hM.exists_isFiniteLocallyFreeData
  refine (SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isColimit M).mpr
    fun W => exists_cover_isColimitCofan_of_coversTop q.X q.coversTop M (fun i => ?_) W
  exact exists_isColimitCofan_of_isIso_generators M (q.X i) (q.generators i)
    (hqfree.isIso i) (hqfin.isFiniteType i).finite

end LocalGenerators

end Stacks.SheafOfModules

end
