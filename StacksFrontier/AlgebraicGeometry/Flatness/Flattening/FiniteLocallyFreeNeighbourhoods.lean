module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Finite local freeness from free neighbourhoods

A sheaf of modules on a scheme which is isomorphic to a finite free module on some open
neighbourhood of every point is finite locally free. The two formulations differ only in
bookkeeping — a choice of neighbourhood at every point *is* a covering together with a free
basis over each member — but the bookkeeping is what
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` asks for, and assembling it is what lets
a pointwise freeness statement be stated the way a source asserting "the module is finitely
locally free" states it.

## Main results

* `AlgebraicGeometry.SheafOfModules.isIso_ofEpi_free_generatingSections_π`: pushing the free
  basis along the inverse of an isomorphism to a free module gives an isomorphism.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_forall_exists_free_nhd`: a module
  with a finite free neighbourhood at every point is finite locally free.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_over_iSup`: the restriction of a module
  to a supremum of opens on each of which it is finite free is finite locally free.

## Implementation notes

The local generators datum is indexed by the points of the scheme, with the chosen
neighbourhood at `x` as the open at index `x`; the covering property holds because every point
lies in its own neighbourhood. The generating family at `x` is the free basis of the chosen free
module, pushed along the inverse of the chosen isomorphism by
`SheafOfModules.GeneratingSections.ofEpi`. Local freeness of that datum is the assertion that
each pushed projection is an isomorphism, which holds because the projection of the generating
sections of a free module is the identity, so the pushed projection is the chosen isomorphism
itself; `AlgebraicGeometry.SheafOfModules.isIso_ofEpi_free_generatingSections_π` isolates that
computation. Finiteness of the generating family is finiteness of `ULift (Fin n)`.

The hypothesis is phrased with `ULift (Fin n)` rather than an arbitrary finite type because that
is the shape in which free neighbourhoods are produced by the fibre-wise freeness criterion
[Stacks, Tag 080Q], which is where such data comes from.

For `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_over_iSup` the same assembly is carried
out one slice down, over the open `⨆ i, W i` rather than over the whole scheme, so the covering
is a covering of that open and the free module over each member is reached through
`AlgebraicGeometry.SheafOfModules.freeOverOverIso`: restricting `F` to `⨆ i, W i` and then to
`W i` is restricting it to `W i`, which is `SheafOfModules.pushforwardPushforwardEquivalence`
for the iterated-slice equivalence. The covering property, which for the whole scheme was the
statement that every point lies in its own neighbourhood, becomes
`AlgebraicGeometry.SheafOfModules.coversTop_iSup`: a sieve on an open of `⨆ i, W i` containing
every `A ⊓ W i` contains the whole open.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- Pushing the generating sections of a free module along the inverse of an isomorphism
`M ≅ free I` gives a generating family whose projection is an isomorphism: the projection of the
generating sections of a free module is the identity, so the pushed projection is the inverse
isomorphism itself. -/
theorem isIso_ofEpi_free_generatingSections_π
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : _root_.SheafOfModules.{u} R} (I : Type u)
    (e : M ≅ _root_.SheafOfModules.free I) :
    IsIso ((( _root_.SheafOfModules.free.generatingSections I).ofEpi e.inv).π) := by
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
    _root_.SheafOfModules.free.generatingSections_π]
  dsimp [_root_.SheafOfModules.free.generatingSections]
  change IsIso (𝟙 (_root_.SheafOfModules.free I) ≫ e.inv)
  simpa only [Category.id_comp] using e.isIso_inv

/-- **A module with a finite free neighbourhood at every point is finite locally free.** The
chosen neighbourhoods cover the scheme, and the free basis over each one, pushed along the
chosen isomorphism, is a finite local free basis. -/
theorem isFiniteLocallyFree_of_forall_exists_free_nhd {X : Scheme.{u}} (F : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ n : ℕ,
      Nonempty (F.over U ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n)))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  choose U hx n e using h
  let q : F.LocalGeneratorsData.{u} :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover, eq_top_iff]
        intro x _
        exact Opens.mem_iSup.mpr ⟨x, hx x⟩
      generators := fun x =>
        (_root_.SheafOfModules.free.generatingSections
          (ULift.{u} (Fin (n x)))).ofEpi (e x).some.inv }
  refine AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} ⟨q, ?_, ?_⟩
  all_goals constructor
  · intro x
    exact isIso_ofEpi_free_generatingSections_π _ _
  · intro x
    exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩

/-- Restricting `F` to an open `V` and then to an open `W` of `V` is restricting it to `W`, so a
free restriction to `W` is a free restriction of `F.over V` to `W`. -/
def freeOverOverIso {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (W : Over V) (n : ℕ)
    (h : F.over W.left ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n))) :
    (F.over V).over W ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n)) := by
  let e := _root_.SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv W)
    (S := (X.ringCatSheaf.over V).over W) (R := X.ringCatSheaf.over W.left)
    (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
  exact e.functor.mapIso h ≪≫
    (_root_.SheafOfModules.mapFreeIso e.functor _ (Iso.refl _)).symm

/-- The opens `W i`, viewed as opens of `⨆ i, W i`, cover `⨆ i, W i`. -/
theorem coversTop_iSup {X : Scheme.{u}} {ι : Type u} (W : ι → X.Opens) :
    ((Opens.grothendieckTopology X).over (⨆ i, W i)).CoversTop
      (fun i => Over.mk (homOfLE (le_iSup W i))) := by
  intro A
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (A.hom.le hx)
  refine ⟨A.left ⊓ W i, homOfLE inf_le_left, ?_, hx, hi⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨i, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩

/-- The local generators data on `⨆ i, W i` given by free restrictions to the `W i`: the opens
`W i` cover it, and the generating family over `W i` is the free basis pushed along the inverse
of the chosen isomorphism. -/
def iSupGenerators {X : Scheme.{u}} (F : X.Modules) {ι : Type u} (W : ι → X.Opens) (n : ι → ℕ)
    (e : ∀ i, F.over (W i) ≅ _root_.SheafOfModules.free (ULift.{u} (Fin (n i)))) :
    (F.over (⨆ i, W i)).LocalGeneratorsData.{u} where
  I := ι
  X := fun i => Over.mk (homOfLE (le_iSup W i))
  coversTop := coversTop_iSup W
  generators := fun i =>
    (_root_.SheafOfModules.free.generatingSections
      (R := (X.ringCatSheaf.over (⨆ i, W i)).over (Over.mk (homOfLE (le_iSup W i))))
      (ULift.{u} (Fin (n i)))).ofEpi (freeOverOverIso F _ _ (n i) (e i)).inv

/-- **A module which is finite free on each of a family of opens is finite locally free on their
union.** This is the form in which a source asserting that a module "restricts to a finitely
locally free module on `V`" states its conclusion, for `V` the union of the opens on which
freeness was found. -/
theorem isFiniteLocallyFree_over_iSup {X : Scheme.{u}} (F : X.Modules) {ι : Type u}
    (W : ι → X.Opens)
    (h : ∀ i, ∃ n : ℕ,
      Nonempty (F.over (W i) ≅ _root_.SheafOfModules.free (ULift.{u} (Fin n)))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F.over (⨆ i, W i)) := by
  choose n e using h
  refine AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
    ⟨iSupGenerators F W n (fun i => (e i).some), ?_, ?_⟩
  all_goals constructor
  · intro i
    exact isIso_ofEpi_free_generatingSections_π _ _
  · intro i
    exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n i))))⟩

end AlgebraicGeometry.SheafOfModules

end
