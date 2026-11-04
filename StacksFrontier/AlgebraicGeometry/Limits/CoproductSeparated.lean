module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness of a coproduct of affine schemes

A disjoint union of affine schemes is a separated scheme.

## Main results

* `AlgebraicGeometry.Scheme.IsSeparated.of_iso`: separatedness of a scheme is invariant under
  isomorphism.
* `AlgebraicGeometry.isSeparated_sigma_of_isAffine`: a coproduct of affine schemes is a
  separated scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Separatedness of a scheme is invariant under isomorphism. -/
theorem Scheme.IsSeparated.of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [Scheme.IsSeparated X] :
    Scheme.IsSeparated Y :=
  ⟨(Subsingleton.elim (e.inv ≫ terminal.from X) (terminal.from Y)) ▸
    (inferInstance : IsSeparated (e.inv ≫ terminal.from X))⟩

/-- A coproduct of affine schemes is a separated scheme. -/
theorem isSeparated_sigma_of_isAffine {J : Type u}
    (Y : J → Scheme.{u}) (hY : ∀ j, IsAffine (Y j)) :
    Scheme.IsSeparated (∐ Y) := by
  let (j : J) : IsAffine (Y j) := hY j
  let R : J → CommRingCat := fun j ↦ (Y j).presheaf.obj (Opposite.op ⊤)
  let e : (∐ Y) ≅ ∐ (fun j ↦ Spec (R j)) := Sigma.mapIso (fun j ↦ (Y j).isoSpec)
  have hc : IsSeparated (e.hom ≫ sigmaSpec R ≫ terminal.from (Spec (.of <| Π j, R j))) :=
    inferInstance
  exact ⟨(Subsingleton.elim (e.hom ≫ sigmaSpec R ≫
    terminal.from (Spec (.of <| Π j, R j))) (terminal.from (∐ Y))) ▸ hc⟩

end AlgebraicGeometry

end
