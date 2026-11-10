module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtensionFunctor
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroPushforward

/-!
# The canonical morphism onto a pushed-forward square-zero extension

`Stacks.Thickenings.SquareZeroExtension.pushforward` turns a square-zero extension `E` of `𝒪_Z`
over `S` into one of `𝒪_V` over `S`, along a morphism `g : Z ⟶ V` whose structure-sheaf
comparison `𝒪_V ⟶ g_*𝒪_Z` is invertible.  The two extensions are not merely related by having
`g_*A` for extension sheaf: `g` *is* a morphism of square-zero extensions from `E` to its
pushforward, in the sense of `Stacks.Thickenings.SquareZeroExtension.Hom`.  This file builds that
morphism and reads off what it gives.

By `Stacks.Thickenings.Realization.map` a morphism of extensions induces a morphism of the
schemes realizing them, so the realization of the pushforward receives a morphism *from* the
realization of `E`, and `Stacks.Thickenings.isIso_c_map_pushforwardHom` says that morphism again
has invertible structure-sheaf comparison.

## Main definitions

* `Stacks.Thickenings.SquareZeroExtension.pushforwardShHom`: the morphism of ringed spaces
  `(Z, A) ⟶ (V, g_*A)`, with underlying map `g` and identity sheaf component.
* `Stacks.Thickenings.SquareZeroExtension.pushforwardHom`: that morphism of ringed spaces together
  with `g`, as a morphism of square-zero extensions over `S`.

## Main results

* `Stacks.Thickenings.SquareZeroExtension.inclusion_eq_homMk` and
  `Stacks.Thickenings.SquareZeroExtension.toBase_eq_homMk`: the inclusion and the structure
  morphism of an extension, written out as morphisms of ringed spaces with prescribed components.
* `Stacks.Thickenings.isIso_hom_c_comp`: invertibility of the sheaf component is stable under
  composition.
* `Stacks.Thickenings.isIso_c_map_pushforwardHom`: **the induced morphism of realizations has
  invertible structure-sheaf comparison.** Hence the realization of the pushforward is again a
  scheme to which the pushforward construction applies.
* `Stacks.Thickenings.immersion_comp_map_pushforwardHom` and
  `Stacks.Thickenings.map_pushforwardHom_comp_toBase`: the induced morphism restricts to `g` on
  the thickened subschemes and lies over `S`.

## Implementation notes

The fields `inclusion_base` and `inclusion_sheaf` of
`Stacks.Thickenings.SquareZeroExtension` pin the inclusion only up to an equality of continuous
maps and a heterogeneous equality of sheaf components, and `over_base` pins the structure
morphism only up to an equality of morphisms of sheafed spaces, so the base map of `toBase` is
the one of `f` only propositionally.  Both compatibility conditions of a morphism of extensions
are equalities of morphisms of ringed spaces whose sheaf components therefore live in types that
agree only propositionally, and `AlgebraicGeometry.SheafedSpace.ext` leaves behind an
`CategoryTheory.eqToHom` that no rewrite removes, because its two sides are equal only after
unfolding the extension.

`Stacks.Thickenings.SquareZeroExtension.inclusion_eq_homMk` and
`Stacks.Thickenings.SquareZeroExtension.toBase_eq_homMk` discharge that once and for all: each
takes the extension apart and substitutes its continuous maps, after which the two sides of the
remaining equation have *syntactically* the same base map and the statement is a
`CategoryTheory.congrArg` in the sheaf component alone.  With the two normal forms in hand both
compatibility conditions are computations on sheaf components, the sheaf component of a composite
of morphisms of ringed spaces being the expected composite on the nose.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {Z V S : Scheme.{u}}

/-! ### The structural morphisms of an extension, in normal form -/

/-- Morphisms of sheafed spaces with the same base map are equal when their sheaf components are. -/
private theorem homMk_congr_c {X Y : SheafedSpace CommRingCat.{u}} (b : X.carrier ⟶ Y.carrier)
    {c c' : Y.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} b).obj X.presheaf}
    (h : c = c') :
    (InducedCategory.homMk (PresheafedSpace.Hom.mk b c) : X ⟶ Y) =
      InducedCategory.homMk (PresheafedSpace.Hom.mk b c') := by
  subst h
  rfl

/-- **The inclusion of an extension, with its components written out.** The canonical map of `X`
into the ringed space carrying the extension sheaf is the identity on points with the quotient
map as sheaf component; the fields `inclusion_base` and `inclusion_sheaf` say so only up to an
equality of continuous maps and a heterogeneous equality, and this is the same statement with
both discharged. -/
theorem SquareZeroExtension.inclusion_eq_homMk {X : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) :
    E.inclusion = (InducedCategory.homMk { base := 𝟙 (X : TopCat), c := E.π.hom } :
      X.toSheafedSpace ⟶ thickenedSpace X E.A) := by
  obtain ⟨A, π, hls, ⟨⟨ibase, ic⟩⟩, hb, hs, tb, ob, I, hq, ι, nat, mk, ek, sz⟩ := E
  replace hb : ibase = 𝟙 (X : TopCat) := hb
  subst hb
  replace hs : ic = π.hom := eq_of_heq hs
  subst hs
  rfl

/-- **The structure morphism of an extension, with its components written out.** Its base map is
the one of `f` — only propositionally, by
`Stacks.Thickenings.SquareZeroExtension.toBase_base` — and its sheaf component read along that
identification is `Stacks.Thickenings.SquareZeroExtension.toBaseC`. -/
theorem SquareZeroExtension.toBase_eq_homMk {X : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) :
    E.toBase = (InducedCategory.homMk { base := f.base, c := E.toBaseC } :
      thickenedSpace X E.A ⟶ S.toSheafedSpace) := by
  obtain ⟨A, π, hls, ⟨⟨ibase, ic⟩⟩, hb, hs, ⟨⟨tbase, tc⟩⟩, ob, I, hq, ι, nat, mk, ek, sz⟩ := E
  replace hb : ibase = 𝟙 (X : TopCat) := hb
  subst hb
  replace hs : ic = π.hom := eq_of_heq hs
  subst hs
  have htb : tbase = f.base :=
    congrArg (fun α : X.toSheafedSpace ⟶ S.toSheafedSpace => α.hom.base) ob
  subst htb
  exact homMk_congr_c _
    ((Category.comp_id tc).symm.trans
      (congrArg (fun t => tc ≫ t) (pushforwardEq_hom_self _ A.presheaf).symm))

/-! ### Invertibility of a sheaf component is stable under composition -/

/-- **The sheaf component of a composite is invertible when both factors' are.** The sheaf
component of a composite of morphisms of ringed spaces is the second one followed by the direct
image of the first, and a functor carries an isomorphism to an isomorphism. -/
theorem isIso_hom_c_comp {X Y W : SheafedSpace CommRingCat.{u}} (a : X ⟶ Y) (b : Y ⟶ W)
    [IsIso a.hom.c] [IsIso b.hom.c] : IsIso (a ≫ b).hom.c := by
  change IsIso (b.hom.c ≫
    (TopCat.Presheaf.pushforward CommRingCat.{u} b.hom.base).map a.hom.c)
  infer_instance

/-! ### `g` as a morphism of extensions onto the pushforward -/

section Pushforward

variable (g : Z ⟶ V) (k : V ⟶ S) (E : SquareZeroExtension (g ≫ k)) [IsIso g.c]
  (hπ : TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
      ≫ structureComparisonInv g))
  (hqc : ((Scheme.Modules.pushforward g).obj E.I).IsQuasicoherent)

/-- **The morphism of ringed spaces onto the pushed-forward extension.** The extension sheaf of
the pushforward is the direct image `g_*A` of the extension sheaf of `E`, so the identity of
`g_*A` is a sheaf component over the continuous map of `g`. -/
def SquareZeroExtension.pushforwardShHom :
    thickenedSpace Z E.A ⟶ thickenedSpace V (E.pushforward g k hπ hqc).A :=
  InducedCategory.homMk { base := g.base, c := 𝟙 _ }

/-- The underlying continuous map of `Stacks.Thickenings.SquareZeroExtension.pushforwardShHom` is
that of `g`. -/
@[simp]
theorem SquareZeroExtension.pushforwardShHom_hom_base :
    (E.pushforwardShHom g k hπ hqc).hom.base = g.base :=
  rfl

/-- The sheaf component of `Stacks.Thickenings.SquareZeroExtension.pushforwardShHom` is the
identity. -/
@[simp]
theorem SquareZeroExtension.pushforwardShHom_hom_c :
    (E.pushforwardShHom g k hπ hqc).hom.c = 𝟙 _ :=
  rfl

/-- The sheaf component of `Stacks.Thickenings.SquareZeroExtension.pushforwardShHom` is an
isomorphism. -/
theorem isIso_pushforwardShHom_hom_c :
    IsIso (E.pushforwardShHom g k hπ hqc).hom.c :=
  IsIso.id _

/-- **`g` is a morphism of square-zero extensions from `E` onto its pushforward.** Its underlying
morphism of schemes is `g` itself and its morphism of ringed spaces is
`Stacks.Thickenings.SquareZeroExtension.pushforwardShHom`. -/
def SquareZeroExtension.pushforwardHom : E.Hom (E.pushforward g k hπ hqc) where
  base := g
  sheafHom := E.pushforwardShHom g k hπ hqc
  inclusion_comm := by
    have hcomp : ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
          ≫ structureComparisonInv g) ≫ g.c
        = (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom :=
      ((Category.assoc _ _ _).trans
        (congrArg
          (fun t => (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom ≫ t)
          (structureComparisonInv_comp_c g))).trans (Category.comp_id _)
    have hc : 𝟙 ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).obj E.A.presheaf) ≫
          (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom =
        ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
            ≫ structureComparisonInv g) ≫ g.c :=
      (Category.id_comp _).trans hcomp.symm
    refine Eq.trans (congrArg (fun q => q ≫ E.pushforwardShHom g k hπ hqc)
      E.inclusion_eq_homMk) ?_
    exact congrArg
      (fun c : ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A).presheaf ⟶
          (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).obj Z.presheaf =>
        (InducedCategory.homMk { base := g.base, c := c } :
          Z.toSheafedSpace ⟶ thickenedSpace V (E.pushforward g k hπ hqc).A)) hc
  toBase_comm := by
    have hmapid : E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
          (𝟙 ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A).presheaf)
        = E.toBaseC :=
      (congrArg
        (fun t : (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).obj
              ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A).presheaf ⟶
            (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).obj
              ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A).presheaf =>
          E.toBaseC ≫ t)
        ((TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map_id
          ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A).presheaf)).trans
        (Category.comp_id E.toBaseC)
    refine Eq.trans ?_ E.toBase_eq_homMk.symm
    exact congrArg
      (fun c : S.presheaf ⟶
          (TopCat.Presheaf.pushforward CommRingCat.{u} (g ≫ k).base).obj E.A.presheaf =>
        (InducedCategory.homMk { base := (g ≫ k).base, c := c } :
          thickenedSpace Z E.A ⟶ S.toSheafedSpace)) hmapid

/-- The underlying morphism of schemes of
`Stacks.Thickenings.SquareZeroExtension.pushforwardHom` is `g`. -/
@[simp]
theorem SquareZeroExtension.pushforwardHom_base :
    (E.pushforwardHom g k hπ hqc).base = g :=
  rfl

/-- The morphism of ringed spaces of `Stacks.Thickenings.SquareZeroExtension.pushforwardHom` is
`Stacks.Thickenings.SquareZeroExtension.pushforwardShHom`. -/
@[simp]
theorem SquareZeroExtension.pushforwardHom_sheafHom :
    (E.pushforwardHom g k hπ hqc).sheafHom = E.pushforwardShHom g k hπ hqc :=
  rfl

/-! ### The induced morphism of realizations -/

variable (r₁ : Realization E) (r₂ : Realization (E.pushforward g k hπ hqc))

/-- **The induced morphism of realizations again has invertible structure-sheaf comparison**:
the morphism from a realization of `E` to a realization of its pushforward induced by
`Stacks.Thickenings.SquareZeroExtension.pushforwardHom` has invertible sheaf component. -/
theorem isIso_c_map_pushforwardHom :
    IsIso (r₁.map r₂ (E.pushforwardHom g k hπ hqc)).c := by
  have : IsIso ((E.pushforwardHom g k hπ hqc).sheafHom).hom.c :=
    isIso_pushforwardShHom_hom_c g k E hπ hqc
  have := isIso_hom_c_comp (E.pushforwardHom g k hπ hqc).sheafHom r₂.sheafedIso.inv
  change IsIso (r₁.sheafedIso.hom ≫
    (E.pushforwardHom g k hπ hqc).sheafHom ≫ r₂.sheafedIso.inv).hom.c
  exact isIso_hom_c_comp _ _

/-- The induced morphism of realizations restricts to `g` on the thickened subschemes. -/
theorem immersion_comp_map_pushforwardHom :
    r₁.immersion ≫ r₁.map r₂ (E.pushforwardHom g k hπ hqc) = g ≫ r₂.immersion :=
  r₁.map_immersion r₂ (E.pushforwardHom g k hπ hqc)

/-- The induced morphism of realizations lies over the base. -/
theorem map_pushforwardHom_comp_toBase :
    r₁.map r₂ (E.pushforwardHom g k hπ hqc) ≫ r₂.toBase = r₁.toBase :=
  r₁.map_toBase r₂ (E.pushforwardHom g k hπ hqc)

end Pushforward

end Stacks.Thickenings

end
