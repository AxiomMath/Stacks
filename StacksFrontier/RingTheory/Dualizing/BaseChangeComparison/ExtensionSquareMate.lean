module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate

/-!
# The comparison of Stacks 065Z is the Beck--Chevalley mate of the extension-of-scalars square

Let

`R ⟶ A`, `R ⟶ R'`, `A ⟶ A'`, `R' ⟶ A'`

be a commutative square of commutative rings, the four rings at four independent universes.
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate` identifies the derived
comparison of [stacks 065Z] with the Beck--Chevalley mate of the square of *restrictions*, taken
along the two extension-of-scalars adjunctions of [stacks 0GMT] at `R → R'` and `A → A'`.  The
other mate description of the same morphism transposes it instead along the adjunctions at
`R → A` and `R' → A'`, where the 2-cell it comes from is the comparison of the two ways of
*extending* scalars around the square.  By `CategoryTheory.iterated_mateEquiv_conjugateEquiv` the
two descriptions differ by a conjugation, so the content of the second one is a single identity
at the level of modules, which this file proves.

The identity, at an `R`-module `M`, equates two morphisms

`R' ⊗_R M ⟶ (A' ⊗_R M)|_{R'}`.

One is the unit of extension of scalars along `R' → A'` followed by the composition isomorphism
of `R → R' → A'`; the other is extension along `R → R'` of the unit along `R → A`, then the
underived comparison of [stacks 065Z], then the composition isomorphism of `R → A → A'`.  Both
send `r' ⊗ m` to `i r' ⊗ m`.

## Main definitions

* `RingTheory.TorIndependence.extendScalarsCompInvOfEq`: degreewise extension of scalars along a
  composite, retargeted along an equality `h ∘ f = hc` of ring homomorphisms; the module-level
  shape of `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq`.

## Main results

* `RingTheory.TorIndependence.unitComp_extendScalarsCompInvOfEq`: the two units of extension of
  scalars, read against the retargeted composition isomorphism, collapse to the unit along the
  composite.
* `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison_fst`: the module-level
  Beck--Chevalley identity for the comparison of [stacks 065Z], along the adjunctions at
  `R → A` and `R' → A'`.

## Implementation notes

The identity is stated without elements, so that it can be used degreewise on a complex: the
three mixed universes of a pure tensor `1 ⊗ (1 ⊗ m)` have no common `Module` instance to
elaborate against.

The universe arguments are pinned explicitly throughout and chosen to agree with those of
`RingTheory.TorIndependence.restrictSquare_unit_comp`.
`ModuleCat.extendRestrictScalarsAdj.{w, u₁, u₂}` only uses `w` through `max w u₂`, so two
spellings of `w` with the same `max w u₂` give the same adjunction but different terms, and a
`rw` with a lemma stated at the other spelling does not fire.

No `@[stacks]` attribute is placed here: [stacks 065Z] is formalized as
`RingTheory.TorIndependence.derivedBaseChangeComparison` and this is a further characterization
of it.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe uR uA uRp uAp v w

section Restrictions

variable {R : Type uR} {R' : Type uRp} {A' : Type uAp} [CommRing R] [CommRing R'] [CommRing A']

/-- **Two composition isomorphisms of restrictions differ by an `eqToHom`.**  Restriction along a
ring map `gf` presented as `i ∘ g` is restriction along `i ∘ g` itself, up to the cast along the
presentation. -/
theorem restrictScalarsComp'_hom_comp_inv (g : R →+* R') (i : R' →+* A')
    {gf : R →+* A'} (hgf : gf = i.comp g) (X : ModuleCat.{w} A') :
    (ModuleCat.restrictScalarsComp'.{w} g i gf hgf).hom.app X ≫
        (ModuleCat.restrictScalarsComp.{w} g i).inv.app X =
      (eqToHom (congrArg ModuleCat.restrictScalars.{w} hgf)).app X := by
  subst hgf; simp

/-- Naturality of the inverse composition isomorphism of restrictions, with the composite functor
on the left already applied. -/
theorem restrictScalarsComp_inv_naturality (g : R →+* R') (i : R' →+* A')
    {X Y : ModuleCat.{w} A'} (u : X ⟶ Y) :
    (ModuleCat.restrictScalars.{w} g).map ((ModuleCat.restrictScalars.{w} i).map u) ≫
        (ModuleCat.restrictScalarsComp.{w} g i).inv.app Y =
      (ModuleCat.restrictScalarsComp.{w} g i).inv.app X ≫
        (ModuleCat.restrictScalars.{w} (i.comp g)).map u :=
  (ModuleCat.restrictScalarsComp.{w} g i).inv.naturality u

/-- Naturality of the cast between two restrictions along equal ring homomorphisms. -/
theorem eqToHom_restrictScalars_naturality {k k' : R →+* A'} (e : k = k')
    {X Y : ModuleCat.{w} A'} (u : X ⟶ Y) :
    (eqToHom (congrArg ModuleCat.restrictScalars.{w} e)).app X ≫
        (ModuleCat.restrictScalars.{w} k').map u =
      (ModuleCat.restrictScalars.{w} k).map u ≫
        (eqToHom (congrArg ModuleCat.restrictScalars.{w} e)).app Y :=
  ((eqToHom (congrArg ModuleCat.restrictScalars.{w} e)).naturality u).symm

/-- **The unit of extension of scalars is compatible with an equality of ring homomorphisms.** -/
theorem unit_extendScalars_eqToHom {k k' : R →+* A'} (e : k = k')
    (M : ModuleCat.{max w uAp} R) :
    (ModuleCat.extendRestrictScalarsAdj.{w, uR, uAp} k).unit.app M ≫
        (eqToHom (congrArg ModuleCat.restrictScalars.{max w uAp} e)).app
            ((ModuleCat.extendScalars.{uR, uAp, max w uAp} k).obj M) ≫
          (ModuleCat.restrictScalars.{max w uAp} k').map
            ((eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp, max w uAp} e)).app M) =
      (ModuleCat.extendRestrictScalarsAdj.{w, uR, uAp} k').unit.app M := by
  subst e; simp

end Restrictions

section CompOfEq

variable {R : Type uR} {A : Type uA} {A' : Type uAp} [CommRing R] [CommRing A] [CommRing A']

/-- **Degreewise extension of scalars along a composite, retargeted along an equality of ring
homomorphisms.**  The module-level counterpart of
`StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq`: the inverse of the composition
isomorphism, followed by the cast along `h ∘ f = hc`. -/
def extendScalarsCompInvOfEq (f : R →+* A) (h : A →+* A') (hc : R →+* A')
    (hfh : h.comp f = hc) :
    ModuleCat.extendScalars.{uR, uA, max v uR uA uAp} f ⋙
        ModuleCat.extendScalars.{uA, uAp, max v uR uA uAp} h ⟶
      ModuleCat.extendScalars.{uR, uAp, max v uR uA uAp} hc :=
  (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{uR, uA, uAp, v} f h).inv ≫
    eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp, max v uR uA uAp} hfh)

/-- **The two units against the retargeted composition isomorphism.**  The unit of extension of
scalars along `f`, then the restriction of the unit along `h`, then the composition isomorphism of
the restrictions, then the restriction of
`RingTheory.TorIndependence.extendScalarsCompInvOfEq`, is the unit of extension of scalars along
`h ∘ f` followed by the cast along `h ∘ f = hc`. -/
theorem unitComp_extendScalarsCompInvOfEq (f : R →+* A) (h : A →+* A') (hc : R →+* A')
    (hfh : h.comp f = hc) (M : ModuleCat.{max v uR uA uAp} R) :
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uAp, uR, uA} f).unit.app M ≫
        (ModuleCat.restrictScalars.{max v uR uA uAp} f).map
            ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA, uA, uAp} h).unit.app
              ((ModuleCat.extendScalars.{uR, uA, max v uR uA uAp} f).obj M)) ≫
          (ModuleCat.restrictScalarsComp.{max v uR uA uAp} f h).inv.app
            ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uAp} h).obj
              ((ModuleCat.extendScalars.{uR, uA, max v uR uA uAp} f).obj M)) ≫
            (ModuleCat.restrictScalars.{max v uR uA uAp} (h.comp f)).map
              ((extendScalarsCompInvOfEq.{uR, uA, uAp, v} f h hc hfh).app M) =
      (ModuleCat.extendRestrictScalarsAdj.{max v uR uA, uR, uAp} (h.comp f)).unit.app M ≫
        (ModuleCat.restrictScalars.{max v uR uA uAp} (h.comp f)).map
          ((eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp,
            max v uR uA uAp} hfh)).app M) := by
  slice_lhs 1 3 => erw [StacksDraft.DerivedExtensionScalarsModelComp.unit_extendScalarsComp'.{uR,
    uA, uAp, v} f h M]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  refine congrArg (fun z => _ ≫ (ModuleCat.restrictScalars.{max v uR uA uAp}
    (h.comp f)).map z) ?_
  simp only [extendScalarsCompInvOfEq, NatTrans.comp_app]
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end CompOfEq

section Square

variable {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- `RingTheory.TorIndependence.restrictSquareIso`, read against the composition isomorphism of
the restrictions along `R → R' → A'`: what survives is the composition isomorphism along
`R → A → A'` and the cast along the commutation of the square. -/
theorem restrictSquareIso_hom_comp_restrictScalarsComp_inv
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)
    (X : ModuleCat.{max v uR uA uRp uAp} A') :
    (restrictSquareIso.{uR, uA, uRp, uAp, v} f g h i sq).hom.app X ≫
        (ModuleCat.restrictScalarsComp.{max v uR uA uRp uAp} g i).inv.app X =
      (ModuleCat.restrictScalarsComp.{max v uR uA uRp uAp} f h).inv.app X ≫
        (eqToHom (congrArg ModuleCat.restrictScalars.{max v uR uA uRp uAp} sq)).app X := by
  simp only [restrictSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [restrictScalarsComp'_hom_comp_inv.{uR, uRp, uAp, max v uR uA uRp uAp} g i sq X]

/-- The cast along `h ∘ f = hc` factors through the cast along the commutation of the square. -/
theorem eqToHom_extendScalars_split {f : R →+* A} {g : R →+* R'} {h : A →+* A'} {i : R' →+* A'}
    {hc : R →+* A'} (h1 : h.comp f = hc) (h2 : i.comp g = hc)
    (M : ModuleCat.{w} R) :
    (eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp, w} h1)).app M =
      (eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp, w} (h1.trans h2.symm))).app M ≫
        (eqToHom (congrArg ModuleCat.extendScalars.{uR, uAp, w} h2)).app M := by
  subst h2; simp

variable (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
  [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).IsLeftAdjoint]
  [(ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).IsLeftAdjoint]
  (hc : R →+* A') (h1 : h.comp f = hc) (h2 : i.comp g = hc)
  (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
  (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
  (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶
    (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶
    (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_g.IsLeftDerivedFunctor alpha_g
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))]
  [L_h.IsLeftDerivedFunctor alpha_h
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))]

include h1 h2 in
/-- **The module-level Beck--Chevalley identity for the comparison of [stacks 065Z], along the
extension-of-scalars adjunctions at `R → A` and `R' → A'`.**

At an `R`-module `M`: the unit of extension of scalars along `R' → A'` at `R' ⊗_R M`, followed by
the composition isomorphism of `R → R' → A'`, equals extension along `R → R'` of the unit along
`R → A`, then the underived comparison of [stacks 065Z] at `A ⊗_R M`, then the composition
isomorphism of `R → A → A'`.  Both carry `r' ⊗ m` to `i r' ⊗ m`. -/
theorem unit_comp_derivedBaseChangeComparison_fst (M : ModuleCat.{max v uR uA uRp uAp} R) :
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uRp, uAp} i).unit.app
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).obj M) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).map
          ((extendScalarsCompInvOfEq.{uR, uRp, uAp, max v uA} g i hc h2).app M) =
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).map
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp uAp, uR, uA} f).unit.app M) ≫
        (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i (h1.trans h2.symm)
            L_g L_h alpha_g alpha_h).1.app
          ((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp uAp} f).obj M) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).map
          ((extendScalarsCompInvOfEq.{uR, uA, uAp, max v uRp} f h hc h1).app M) := by
  have hgi := unitComp_extendScalarsCompInvOfEq.{uR, uRp, uAp, max v uA} g i hc h2 M
  have hfh := unitComp_extendScalarsCompInvOfEq.{uR, uA, uAp, max v uRp} f h hc h1 M
  refine ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp, uR, uRp} g).homEquiv
    _ _).injective ?_
  refine (cancel_mono ((ModuleCat.restrictScalarsComp.{max v uR uA uRp uAp} g i).inv.app
    ((ModuleCat.extendScalars.{uR, uAp, max v uR uA uRp uAp} hc).obj M))).mp ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => rw [restrictScalarsComp_inv_naturality.{uR, uRp, uAp,
    max v uR uA uRp uAp} g i]
  rw [hgi]
  slice_rhs 4 5 => rw [restrictScalarsComp_inv_naturality.{uR, uRp, uAp,
    max v uR uA uRp uAp} g i]
  slice_rhs 1 2 => rw [Adjunction.unit_naturality]
  have hsq := restrictSquare_unit_comp.{uR, uA, uRp, uAp, v} f g h i (h1.trans h2.symm)
    L_g L_h alpha_g alpha_h ((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp uAp} f).obj M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hsq ⊢
  slice_rhs 2 3 => rw [← hsq]
  simp only [Category.assoc]
  slice_rhs 3 4 => rw [restrictSquareIso_hom_comp_restrictScalarsComp_inv.{uR, uA, uRp, uAp, v}
    f g h i (h1.trans h2.symm)]
  slice_rhs 4 5 => rw [eqToHom_restrictScalars_naturality.{uR, uAp,
    max v uR uA uRp uAp} (h1.trans h2.symm)]
  slice_rhs 1 4 => rw [hfh]
  slice_rhs 2 3 => rw [← eqToHom_restrictScalars_naturality.{uR, uAp,
    max v uR uA uRp uAp} (h1.trans h2.symm)]
  rw [eqToHom_extendScalars_split.{uR, uA, uRp, uAp, max v uR uA uRp uAp} h1 h2 M,
    CategoryTheory.Functor.map_comp]
  slice_rhs 1 3 => rw [unit_extendScalars_eqToHom.{uR, uAp,
    max v uR uA uRp} (h1.trans h2.symm) M]

end Square

end RingTheory.TorIndependence

end
