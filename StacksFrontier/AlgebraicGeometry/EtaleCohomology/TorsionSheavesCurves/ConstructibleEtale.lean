module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible abelian sheaves on Mathlib's small étale site

The constructibility predicate of Stacks Tag 03RW,
`AlgebraicGeometry.IsConstructibleAbelianSheaf`, is defined for sheaves on the small étale site
of Stacks Tag 021B: the category of schemes étale over `X` that lie in a fixed big étale site
`B`. Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology` has the same sheaves, by
`AlgebraicGeometry.SmallEtale.sheafEquiv`. This file transports the predicate along that
equivalence.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleSmallEtaleSheaf`: an abelian sheaf on Mathlib's small
  étale site of `X` is constructible when, for some big étale site `B` containing `X`, the
  corresponding sheaf on the small étale site of Tag 021B is constructible in the sense of Tag
  03RW.
* `Stacks.EtaleCohomology.IsConstructibleEtaleSheafIn`: constructibility with respect to a fixed
  big étale site `B` containing `X`.

## Main results

* `Stacks.EtaleCohomology.IsConstructibleEtaleSheafIn.of_iso`, `.of_mono`, `.of_epi`,
  `.of_shortExact`, `.outer_of_shortExact`: constructibility with respect to a fixed big étale site
  is invariant under isomorphism, passes to subsheaves and quotient sheaves on a Noetherian scheme
  (Stacks Tag 09BH (2)), to the middle term of a short exact sequence (Stacks Tag 03RZ (2)), and to
  the outer terms of a short exact sequence on a Noetherian scheme.

## Implementation notes

The small étale site of the source is the one cut out of a big étale site (Tag 021B), and the
definition reads constructibility there, so it is the source's definition. The big étale site is
existentially quantified: a statement with constructibility as a hypothesis is then at its
strongest, and the theory of constructible sheaves, which is developed for a fixed `B`, applies to
the witness.

The coefficient universe is `u + 1` for schemes in `Scheme.{u}`: it is the universe of the sets of
sections of a sheaf on either presentation of the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Constructibility of an abelian sheaf on Mathlib's small étale site (Stacks Tag 03RW).** For
some big étale site `B` containing `X`, the sheaf corresponds under
`AlgebraicGeometry.SmallEtale.sheafEquiv` to a constructible abelian sheaf on the small étale site
of `X` cut out of `B`. -/
def IsConstructibleSmallEtaleSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∃ (B : BigEtaleSite.{u}) (hX : B.Contains X),
    IsConstructibleAbelianSheaf B (B.obj X hX)
      ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj F)

variable {X : Scheme.{u}}

/-- The sheaf on the small étale site of Stacks Tag 021B corresponding to an abelian sheaf on
Mathlib's small étale site, for a big étale site `B` containing `X`. -/
abbrev toBoundedSiteAb (B : BigEtaleSite.{u}) (hX : B.Contains X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1} :=
  (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse

/-- Constructibility with respect to a fixed big étale site `B` containing `X`. -/
def IsConstructibleEtaleSheafIn (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  IsConstructibleAbelianSheaf B (B.obj X hX) ((toBoundedSiteAb B hX).obj F)

/-- An abelian sheaf on Mathlib's small étale site of `X` is constructible if and only if it is
constructible with respect to some big étale site `B` containing `X`. -/
theorem isConstructibleEtaleSheaf_iff (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleSmallEtaleSheaf F ↔ ∃ (B : BigEtaleSite.{u}) (hX : B.Contains X),
      IsConstructibleEtaleSheafIn B hX F :=
  Iff.rfl

namespace IsConstructibleEtaleSheafIn

variable {B : BigEtaleSite.{u}} {hX : B.Contains X}

/-- Constructibility is invariant under isomorphism. -/
theorem of_iso {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : IsConstructibleEtaleSheafIn B hX F) : IsConstructibleEtaleSheafIn B hX G :=
  isConstructibleAbelianSheaf_congr B (B.obj X hX) ((toBoundedSiteAb B hX).mapIso e) hF

/-- **Stacks Tag 09BH (2), subsheaves.** On a Noetherian scheme a subsheaf of a constructible
abelian sheaf is constructible. -/
theorem of_mono [IsNoetherian X] {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleEtaleSheafIn B hX F) :
    IsConstructibleEtaleSheafIn B hX G :=
  have : IsNoetherian (B.obj X hX).obj := ‹IsNoetherian X›
  isConstructibleAbelianSheaf_of_mono B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX))
    (representableIsConstructibleSetSheaf B (B.obj X hX))
    (hasFiniteRepresentableCover B (B.obj X hX)) ((toBoundedSiteAb B hX).map i) hF

/-- **Stacks Tag 09BH (2), quotients.** On a Noetherian scheme a quotient sheaf of a
constructible abelian sheaf is constructible. -/
theorem of_epi [IsNoetherian X] {F Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (p : F ⟶ Q) [Epi p] (hF : IsConstructibleEtaleSheafIn B hX F) :
    IsConstructibleEtaleSheafIn B hX Q :=
  have : IsNoetherian (B.obj X hX).obj := ‹IsNoetherian X›
  isConstructibleAbelianSheaf_of_epi B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX))
    (representableIsConstructibleSetSheaf B (B.obj X hX))
    (hasFiniteRepresentableCover B (B.obj X hX)) ((toBoundedSiteAb B hX).map p) hF

/-- **Stacks Tag 03RZ (2), extensions.** The middle term of a short exact sequence whose outer
terms are constructible is constructible. -/
@[sga "4 IX 2.6" "(ii), special case"]
theorem of_shortExact {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (h₁ : IsConstructibleEtaleSheafIn B hX S.X₁)
    (h₃ : IsConstructibleEtaleSheafIn B hX S.X₃) : IsConstructibleEtaleSheafIn B hX S.X₂ :=
  isConstructibleAbelianSheaf_of_shortExact B (B.obj X hX) (S := S.map (toBoundedSiteAb B hX))
    (hS.map_of_exact (toBoundedSiteAb B hX)) h₁ h₃

/-- The outer terms of a short exact sequence with constructible middle term are constructible,
on a Noetherian scheme. -/
@[sga "4 IX 2.6" "(i bis), special case"]
theorem outer_of_shortExact [IsNoetherian X]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (h₂ : IsConstructibleEtaleSheafIn B hX S.X₂) :
    IsConstructibleEtaleSheafIn B hX S.X₁ ∧ IsConstructibleEtaleSheafIn B hX S.X₃ :=
  have := hS.mono_f
  have := hS.epi_g
  ⟨of_mono S.f h₂, of_epi S.g h₂⟩

end IsConstructibleEtaleSheafIn

end Stacks.EtaleCohomology

end
