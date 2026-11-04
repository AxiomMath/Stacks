module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# An isomorphism of schemes induces an isomorphism of `RingCat`-valued structure sheaves

For a morphism of schemes `f : X ⟶ Y`, `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom f`
whiskers the comparison map `f.c` of structure sheaves with `forget₂ CommRingCat RingCat`.
When `f` is an isomorphism this morphism of sheaves of rings is an isomorphism too.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- If `f : X ⟶ Y` is an isomorphism of schemes, the induced morphism
`Y.ringCatSheaf ⟶ f.base _* X.ringCatSheaf` of sheaves of rings is an isomorphism. -/
instance isIso_toRingCatSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso f.toRingCatSheafHom := by
  have hc : IsIso f.c := PresheafedSpace.c_isIso_of_iso f.toPshHom
  have : IsIso ((TopCat.Sheaf.forget RingCat.{u} _).map f.toRingCatSheafHom) :=
    inferInstanceAs
      (IsIso (Functor.whiskerRight f.c (CategoryTheory.forget₂ CommRingCat RingCat.{u})))
  exact isIso_of_reflects_iso _ (TopCat.Sheaf.forget RingCat.{u} _)

/-- `isIso_toRingCatSheafHom`, stated for the category `Sheaf (Opens.grothendieckTopology Y)
RingCat` of sheaves of rings on the site of opens of `Y`; `TopCat.Sheaf RingCat Y` is the same
category, but the two spellings are distinct keys for instance search. -/
instance isIso_toRingCatSheafHom' {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso (C := Sheaf (_root_.Opens.grothendieckTopology ↥Y) RingCat.{u})
      f.toRingCatSheafHom :=
  isIso_toRingCatSheafHom f

example {Y Y' : Scheme.{u}} (v : Y ≅ Y') : IsIso v.hom.toRingCatSheafHom := inferInstance

end AlgebraicGeometry.Scheme
