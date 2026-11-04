module

public import StacksFrontier.CategoryTheory.Localization.ModelComparisonCounit

/-!
# Composition of model comparisons, with the second model postcomposed

`Stacks.CategoryTheory.ModelComparison.comp_comm` compares two models `Q₁`, `Q₂` of the
localization of one underived category.  The case that occurs when the second model is the first
one followed by an equivalence `E` of the targets — `Q₂ = Q₁ ⋙ E`, the comparison of the two
localizations being the identity — is recorded here separately, because that is the shape a
consumer which *transports* the second comparison along `E` produces: the comparison
`Q₁ ⋙ E ⋙ L₂ ⟶ p ⋙ Q₁ ⋙ E`, and the factorisation of the comparison isomorphism with no
intervening identity.

## Main results

* `Stacks.CategoryTheory.ModelComparison.comp_comm_postcomp`: `comp_comm` for `Q₂ = Q₁ ⋙ E`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.ModelComparison

variable {HX HY HZ D₁X D₁Y D₁Z D₂X D₂Y D₂Z : Type*} [Category HX] [Category HY] [Category HZ]
  [Category D₁X] [Category D₁Y] [Category D₁Z] [Category D₂X] [Category D₂Y] [Category D₂Z]
  {Q₁X : HX ⥤ D₁X} {Q₁Y : HY ⥤ D₁Y} {Q₁Z : HZ ⥤ D₁Z}
  {EX : D₁X ⥤ D₂X} {EY : D₁Y ⥤ D₂Y} {EZ : D₁Z ⥤ D₂Z}
  {pf : HY ⥤ HX} {pg : HZ ⥤ HY} {pc : HZ ⥤ HX}
  {L₁f : D₁Y ⥤ D₁X} {L₁g : D₁Z ⥤ D₁Y} {L₁c : D₁Z ⥤ D₁X}
  {L₂f : D₂Y ⥤ D₂X} {L₂g : D₂Z ⥤ D₂Y} {L₂c : D₂Z ⥤ D₂X}

/-- **`Stacks.CategoryTheory.ModelComparison.comp_comm` with the second model postcomposed.**
The second localization is the first followed by `E`, the comparisons `c₂` of the second model are
stated for that composite, and the factorisations `hf`, `hg`, `hc` of the comparison isomorphisms
carry no identity.  The conclusion is unchanged: the comparison isomorphism of the composite is
the composite of the comparison isomorphisms. -/
theorem comp_comm_postcomp (e : pg ⋙ pf ≅ pc) (C₁ : L₁g ⋙ L₁f ≅ L₁c) (C₂ : L₂g ⋙ L₂f ≅ L₂c)
    (c₁f : Q₁Y ⋙ L₁f ⟶ pf ⋙ Q₁X) (c₁g : Q₁Z ⋙ L₁g ⟶ pg ⋙ Q₁Y) (c₁c : Q₁Z ⋙ L₁c ⟶ pc ⋙ Q₁X)
    (c₂f : Q₁Y ⋙ EY ⋙ L₂f ⟶ pf ⋙ Q₁X ⋙ EX) (c₂g : Q₁Z ⋙ EZ ⋙ L₂g ⟶ pg ⋙ Q₁Y ⋙ EY)
    (c₂c : Q₁Z ⋙ EZ ⋙ L₂c ⟶ pc ⋙ Q₁X ⋙ EX)
    (φf : L₁f ⋙ EX ≅ EY ⋙ L₂f) (φg : L₁g ⋙ EY ≅ EZ ⋙ L₂g) (φc : L₁c ⋙ EX ≅ EZ ⋙ L₂c)
    (h₁ : ∀ M : HZ, C₁.hom.app (Q₁Z.obj M) ≫ c₁c.app M =
      L₁f.map (c₁g.app M) ≫ c₁f.app (pg.obj M) ≫ Q₁X.map (e.hom.app M))
    (h₂ : ∀ M : HZ, C₂.hom.app (EZ.obj (Q₁Z.obj M)) ≫ c₂c.app M =
      L₂f.map (c₂g.app M) ≫ c₂f.app (pg.obj M) ≫ EX.map (Q₁X.map (e.hom.app M)))
    (hf : ∀ M : HY, φf.hom.app (Q₁Y.obj M) ≫ c₂f.app M = EX.map (c₁f.app M))
    (hg : ∀ M : HZ, φg.hom.app (Q₁Z.obj M) ≫ c₂g.app M = EY.map (c₁g.app M))
    (hc : ∀ M : HZ, φc.hom.app (Q₁Z.obj M) ≫ c₂c.app M = EX.map (c₁c.app M))
    (hres : ∀ K : D₁Z, ∃ (M : HZ) (_ : K ≅ Q₁Z.obj M), IsIso (c₁c.app M))
    (K : D₁Z) :
    C₂.hom.app (EZ.obj K) ≫ φc.inv.app K =
      L₂f.map (φg.inv.app K) ≫ φf.inv.app (L₁g.obj K) ≫ EX.map (C₁.hom.app K) :=
  comp_comm (Q₂X := Q₁X ⋙ EX) (Q₂Y := Q₁Y ⋙ EY) (Q₂Z := Q₁Z ⋙ EZ)
    (κX := Iso.refl _) (κY := Iso.refl _) (κZ := Iso.refl _) e C₁ C₂ c₁f c₁g c₁c c₂f c₂g c₂c
    φf φg φc h₁ h₂ (by simpa using hf ·) (by simpa using hg ·)
    (by simpa using hc ·) hres K

end Stacks.CategoryTheory.ModelComparison

end
