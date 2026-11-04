module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinCase
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria

/-!
# The set-theoretic fibre over the image of the curve

In the Stein case of [Stacks, Tag 0C2L] — `f : X ⟶ Y` proper with geometrically connected fibres,
carrying the closed subscheme `E` cut out by `D` to a point `y`, and quasi-finite at every point
off `E` — the fibre `f⁻¹(y)` is exactly `E` as a set.

A point of the fibre at which `f` is quasi-finite is isolated and closed in its fibre
([Stacks, Tag 01TH]), so it is clopen in the connected fibre and is therefore the whole fibre;
since the fibre also contains the nonempty set `E`, no point off `E` lies in it.

## Main results

* `AlgebraicGeometry.preimage_singleton_subset_of_quasiFiniteAt`: a connected fibre containing a
  nonempty set `S` contains no point off `S` at which the morphism is quasi-finite.
* `AlgebraicGeometry.preimage_singleton_subset_support_of_steinSetup`: in the Stein case of
  [Stacks, Tag 0C2L] the fibre over `y` is contained in the support of `D`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A connected fibre containing a nonempty set `S` contains no point off `S` at which the
morphism is quasi-finite. -/
public theorem preimage_singleton_subset_of_quasiFiniteAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [GeometricallyConnected f] (y : Y) (S : Set X) (hS : S.Nonempty)
    (hmaps : ∀ x ∈ S, f.base x = y) (hqf : ∀ x ∉ S, quasiFiniteAt f x) :
    f.base ⁻¹' {y} ⊆ S := by
  intro x hx
  by_contra hxS
  have hfx : f.base x = y := hx
  have hqfx := hqf x hxS
  have hopen : IsOpen ({f.asFiber x} : Set (f.fiber (f.base x))) :=
    (isIsolatedPoint_iff _).mp (((quasiFiniteAt_tfae f x).out 1 2).mp hqfx)
  have h3 : IsClosed ({f.asFiber x} : Set (f.fiber (f.base x))) ∧
      ¬ ∃ x' : f.fiber (f.base x), x' ≠ f.asFiber x ∧ x' ⤳ f.asFiber x :=
    ((quasiFiniteAt_tfae f x).out 1 3).mp hqfx
  have huniv : ({f.asFiber x} : Set (f.fiber (f.base x))) = Set.univ :=
    (isClopen_iff.mp ⟨h3.1, hopen⟩).resolve_left (Set.singleton_nonempty _).ne_empty
  obtain ⟨z, hz⟩ := hS
  have hzfib : f.base z = f.base x := (hmaps z hz).trans hfx.symm
  let z' : f.fiber (f.base x) := (f.fiberHomeo (f.base x)).symm ⟨z, hzfib⟩
  have hz' : z' = f.asFiber x :=
    (huniv ▸ Set.mem_univ z' : z' ∈ ({f.asFiber x} : Set (f.fiber (f.base x))))
  have hzx : z = x := by
    have h1 : f.fiberι (f.base x) z' = z := f.fiberι_fiberHomeo_symm _ _
    rw [hz', Scheme.Hom.fiberι_asFiber] at h1
    exact h1.symm
  exact hxS (hzx ▸ hz)

/-- In the Stein case of [Stacks, Tag 0C2L] the fibre over `y` is contained in the support of
`D`. -/
public theorem preimage_singleton_subset_support_of_steinSetup {X Y : Scheme.{u}}
    {D : X.IdealSheafData} {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y) :
    f.base ⁻¹' {y} ⊆ (D.support : Set X) := by
  have := hsetup.isProper
  have := hsetup.geometricallyConnected
  have hne : (D.support : Set X).Nonempty :=
    (D.isConnected_support_of_iso_projectiveLineProj k e).nonempty
  exact preimage_singleton_subset_of_quasiFiniteAt f y _ hne
    ((D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hsetup.base_eq)
    hsetup.quasiFinite_of_notMem

end AlgebraicGeometry

end
