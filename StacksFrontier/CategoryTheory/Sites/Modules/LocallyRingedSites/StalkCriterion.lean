module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.LocalRing.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project Lemma 18.40.8, Tag 04H9.

We work with ringed topoi arising from sites. Fix a morphism of ringed topoi
`(f, f^#) : (Sh(C), O_C) -> (Sh(D), O_D)`, where `C`, `D` are sites, `Sh(C)`, `Sh(D)`
are their topoi of sheaves of sets, and `O_C`, `O_D` are sheaves of commutative
(unital) rings on `C`, `D` respectively.

For a sheaf of rings `O` the units sheaf `O^*` is the subsheaf of units: the
sheafification of the presheaf `U |-> O(U)^*`. For a point `p` the stalk `O_p` is a
ring with `(O^*)_p = (O_p)^*` (because `p^{-1}` is exact, hence preserves the
cartesian square defining the units). The composite point `q = f . p` and the map
`f^#` induce a ring homomorphism on stalks `phi_p : O_{D,q} -> O_{C,p}`.

The theorem asserts relations between:
* (1) a cartesian square of sheaves of sets on `C` relating the units sheaves and
      ring sheaves pulled back along `f`;
* (2) for every point `p` of `C`, a cartesian square of sets relating the
      unit-stalks and ring-stalks via `phi_p`;
* (3) (locally ringed case) for every point `p`, the stalk map `phi_p` is a local
      ring map;
together with the role of "enough points" / conservative families.

The published proof reads in full: "This lemma proves itself, in other words, it
follows by unwinding the definitions."

All rings are commutative with identity. We do not assume `D` has enough points
anywhere; only hypotheses on `C` (enough points / a conservative family) and on the
locally-ringed character of the two topoi are used.

## Design notes (faithfulness)

The canonical objects and maps attached to a sheaf of rings `O` are:

* `unitsToType : CommRingCat ⥤ Type` sends `R` to `Rˣ` (its underlying set), built
  from the genuine group-of-units functor `MonCat.units`; `unitsIncl` is the
  canonical inclusion `Rˣ -> R`.
* `unitsSheafFunctor` sends a sheaf of rings `O` to its units sheaf `O^*`, defined as
  the *sheafification* of the presheaf of units `U |-> O(U)ˣ`. Functorial in `O`, so
  the maps in condition (1) are induced canonically by `f^#`.
* `OsetFunctor` sends a sheaf of rings to its underlying sheaf of sets.
* `unitsInclSheaf` is the canonical inclusion of sheaves `O^* -> O_set`, the
  sheafification of `unitsIncl`.

The canonical identifications

* `(O^*)_p = (O_p)^*`  (the stalk of the units sheaf is the unit group of the stalk
  ring, Stacks Lemma 18.40.11 / exactness of `p^{-1}`), and
* `f^{-1}(O_D^*) = (f^{-1}O_D)^*`  (the inverse image of the units sheaf is the units
  sheaf of the inverse image, Stacks Lemma 18.40.11 / exactness of `f^{-1}`),

are part of the *data* of a `Point` and a `RingedToposHom` respectively (carried as
named natural isomorphisms `stalkUnitsIso`, `finvUnitsIso`), together with
*compatibility axioms* requiring them to commute with the canonical unit inclusions.
This pins them down as the canonical identifications and lets the literal squares in
conditions (1) and (2) be stated with the top-left objects `f^{-1}(O_D^*)` and
`(O_D^*)_q = stalk_q(O_D^*)` exactly as in the source.

The locally ringed condition (Definition 7) is formalized intrinsically: condition (1)
of Definition 7 is the sections-level statement "on every object `U` that is not
sheaf-theoretically empty (the empty sieve does not cover `U`), the sections `0` and
`1` of `O(U)` are distinct"; condition (2) is the local "unit or co-unit" condition.
The standard consequence that each stalk of a locally ringed topos is a local ring is
recorded by the field `isLocalRing_stalk`, which (per Stacks 18.40) holds at every
individual point under the locally ringed hypothesis alone, with no enough-points
assumption.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Sheaves.LocallyRingedTopos

/-! ## The canonical units functor on commutative rings.

`unitsToType` is the functor `CommRingCat ⥤ Type` sending a ring `R` to its set of
units `Rˣ`, built from the genuine group-of-units functor `MonCat.units`.
`unitsIncl` is the canonical natural inclusion `Rˣ ↪ R`. -/

/-- The functor `CommRingCat ⥤ Type` sending `R` to its group of units `Rˣ`
(as a set). -/
noncomputable def unitsToType : CommRingCat.{u} ⥤ Type u :=
  forget₂ CommRingCat CommMonCat ⋙ forget₂ CommMonCat MonCat ⋙ MonCat.units ⋙ forget GrpCat

/-- The canonical inclusion of units `Rˣ ↪ R`, as a natural transformation
`unitsToType ⟶ forget CommRingCat`. -/
noncomputable def unitsIncl : unitsToType.{u} ⟶ forget CommRingCat.{u} where
  app R := ↾(fun (u : unitsToType.obj R) => @Units.val R _ u)
  naturality := by intro R S f; rfl

/-! ## Ringed topos over a site (Definition 1, object part).

A ringed topos is a site `(C, J)` together with a sheaf of commutative (unital)
rings `O`. Its topos of sheaves of sets is `Sheaf J (Type u)`. -/

/-- A ringed topos: a site `(C, J)` together with a sheaf of commutative rings. -/
@[sga "4 IV 11.1.1" "special case"]
structure RingedTopos where
  /-- the underlying category of the site -/
  C : Type u
  [cat : Category.{u} C]
  /-- the Grothendieck topology -/
  J : GrothendieckTopology C
  /-- the structure sheaf of rings -/
  O : Sheaf J CommRingCat.{u}

attribute [instance] RingedTopos.cat

namespace RingedTopos

variable (X : RingedTopos.{u})

/-- The topos of sheaves of sets of a ringed topos. -/
abbrev Topos : Type _ := Sheaf X.J (Type u)

/-- The functor sending a sheaf of rings on the site of `X` to its underlying sheaf
of sets. -/
noncomputable abbrev OsetFunctor : Sheaf X.J CommRingCat.{u} ⥤ X.Topos :=
  sheafCompose X.J (forget CommRingCat.{u})

/-- The presheaf-of-units functor: a sheaf of rings to the presheaf `U ↦ O(U)ˣ`. -/
noncomputable def unitsPreFunctor : Sheaf X.J CommRingCat.{u} ⥤ (X.Cᵒᵖ ⥤ Type u) :=
  sheafToPresheaf X.J CommRingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj unitsToType

/-- The **units sheaf functor**: sends a sheaf of rings `O` to the units sheaf `O^*`,
the sheafification of the presheaf of units `U ↦ O(U)ˣ`. Functorial in `O`, hence the
maps it induces are canonical. -/
noncomputable def unitsSheafFunctor : Sheaf X.J CommRingCat.{u} ⥤ X.Topos :=
  X.unitsPreFunctor ⋙ presheafToSheaf X.J (Type u)

/-- The underlying sheaf of sets of the structure sheaf `O_X`. -/
noncomputable abbrev Oset : X.Topos := X.OsetFunctor.obj X.O

/-- The units sheaf `O_X^*` of the structure sheaf. -/
noncomputable abbrev units : X.Topos := X.unitsSheafFunctor.obj X.O

/-- The canonical inclusion of sheaves `O^* ↪ O_set` for a sheaf of rings `O`,
obtained by sheafifying the canonical units inclusion `unitsIncl`. -/
noncomputable def unitsInclSheaf (O : Sheaf X.J CommRingCat.{u}) :
    X.unitsSheafFunctor.obj O ⟶ X.OsetFunctor.obj O :=
  (presheafToSheaf X.J (Type u)).map (Functor.whiskerLeft O.obj unitsIncl) ≫
    (sheafificationIso (X.OsetFunctor.obj O)).inv

end RingedTopos

/-! ## Morphisms of ringed topoi -/

/-- A morphism of ringed topoi `(f, f^#) : (Sh(C), O_C) -> (Sh(D), O_D)` consists of:
* a morphism of topoi `f`, i.e. an adjoint pair `(f^{-1}, f_*)` with `f^{-1}` left
  adjoint to `f_*` and `f^{-1}` exact (preserves finite limits and all colimits), on
  sheaves of sets;
* a lift `finvRing` of `f^{-1}` to sheaves of rings (the inverse image of internal
  rings is a ring), compatible with `f^{-1}` after forgetting to sets;
* the canonical identification `f^{-1}(O_D^*) = (f^{-1}O_D)^*` (`finvUnitsIso`), a
  natural isomorphism compatible with the unit inclusions (`finvUnitsIso_compat`),
  recording Stacks Lemma 18.40.11; together with
* a homomorphism of sheaves of rings `f^# : f^{-1} O_D -> O_C`, i.e. a morphism
  `finvRing.obj O_D ⟶ O_C`. -/
structure RingedToposHom (X Y : RingedTopos.{u}) where
  /-- inverse image functor `f^{-1}` on sheaves of sets -/
  finv : Y.Topos ⥤ X.Topos
  /-- direct image functor `f_*` on sheaves of sets -/
  fdir : X.Topos ⥤ Y.Topos
  /-- the adjunction `f^{-1} ⊣ f_*` -/
  adj : finv ⊣ fdir
  /-- `f^{-1}` is left exact (preserves finite limits) -/
  invPreservesFiniteLimits : PreservesFiniteLimits finv
  /-- `f^{-1}` preserves all colimits -/
  invPreservesColimits : PreservesColimits finv
  /-- the lift `f^{-1}_ring` of `f^{-1}` to sheaves of rings -/
  finvRing : Sheaf Y.J CommRingCat.{u} ⥤ Sheaf X.J CommRingCat.{u}
  /-- compatibility: forgetting `f^{-1}_ring O` to sets agrees with `f^{-1}` of the
      underlying sheaf of sets of `O` -/
  finvRing_compat : finvRing ⋙ X.OsetFunctor ≅ Y.OsetFunctor ⋙ finv
  /-- the canonical identification `f^{-1}(O_D^*) ≅ (f^{-1} O_D)^*` (Stacks Lemma
      18.40.11), as a natural isomorphism `O_D^* ↦ f^{-1}(O_D^*)` vs.
      `O_D ↦ (f^{-1}O_D)^*`. -/
  finvUnitsIso : Y.unitsSheafFunctor ⋙ finv ≅ finvRing ⋙ X.unitsSheafFunctor
  /-- the comparison `f^# : f^{-1} O_D -> O_C` of sheaves of rings -/
  fSharp : finvRing.obj Y.O ⟶ X.O
  /-- compatibility axiom pinning down `finvUnitsIso` as the canonical identification:
      for every sheaf of rings `O` on `D`, the iso commutes with the unit inclusions,
      i.e. the square relating `f^{-1}(O^* ↪ O)` and `(f^{-1}O)^* ↪ f^{-1}O` commutes. -/
  finvUnitsIso_compat : ∀ O : Sheaf Y.J CommRingCat.{u},
    (finvUnitsIso.app O).hom ≫ X.unitsInclSheaf (finvRing.obj O) ≫ (finvRing_compat.app O).hom
      = finv.map (Y.unitsInclSheaf O)

attribute [instance] RingedToposHom.invPreservesFiniteLimits
attribute [instance] RingedToposHom.invPreservesColimits

namespace RingedToposHom

variable {X Y : RingedTopos.{u}} (f : RingedToposHom X Y)

/-- The underlying map of sheaves of sets of `f^# : f^{-1} O_D -> O_C`. -/
noncomputable def fSharpSet : f.finv.obj Y.Oset ⟶ X.Oset :=
  (f.finvRing_compat.symm.app Y.O).hom ≫ X.OsetFunctor.map f.fSharp

/-- The induced map on units sheaves `f^{-1}(O_D^*) ⟶ O_C^*`, using the canonical
identification `f^{-1}(O_D^*) ≅ (f^{-1}O_D)^*` and then `f^#` on units. This is the
top horizontal arrow of condition (1). -/
noncomputable def fSharpUnits : f.finv.obj Y.units ⟶ X.units :=
  (f.finvUnitsIso.app Y.O).hom ≫ X.unitsSheafFunctor.map f.fSharp

end RingedToposHom

/-! ## Condition (1) -/

/-- Condition (1): the square of sheaves of sets on `C`
```
  f^{-1}(O_D^*) --(f^#)--> O_C^*
  | f^{-1}(incl)            | incl
  v                         v
  f^{-1}(O_D)   --f^#-->    O_C
```
is cartesian. The top-left corner is literally `f^{-1}(O_D^*) =
f.finv.obj Y.units`; the left vertical arrow is `f^{-1}` of the unit inclusion
`O_D^* ↪ O_D`; the top horizontal arrow `fSharpUnits` is `f^#` on units (via the
canonical identification `f^{-1}(O_D^*) = (f^{-1}O_D)^*`); the bottom arrow is
`fSharpSet`; the right vertical arrow is the unit inclusion `O_C^* ↪ O_C`. -/
def Condition1 {X Y : RingedTopos.{u}} (f : RingedToposHom X Y) : Prop :=
  IsPullback
    (f.fSharpUnits)
    (f.finv.map (Y.unitsInclSheaf Y.O))
    (X.unitsInclSheaf X.O)
    (f.fSharpSet)

/-! ## Points and stalks -/

/-- A point `p` of `(C, J)` is a stalk functor `p^{-1} = (.)_p : Sh(C) -> Sets` that is
exact (preserves finite limits and all colimits) and admits a right adjoint `p_*`.
Because the stalk functor preserves finite limits, it carries internal ring sheaves
to rings; we record this through a lift `stalkRing` of the stalk functor to a functor
`Sh_ring(C) -> CommRingCat` compatible with `p^{-1}` after forgetting. The stalk of
`O_C` at `p` is the ring `stalkRing.obj O_C`, written `O_{C,p}`.

The identification `(O^*)_p = (O_p)^*` (Stacks Lemma 18.40.11) is part of the data:
the natural isomorphism `stalkUnitsIso`, pinned down by the compatibility axiom
`stalkUnitsIso_compat` requiring it to commute with the unit inclusions. -/
structure Point (X : RingedTopos.{u}) where
  /-- the stalk functor `p^{-1} : Sh(C) -> Sets` -/
  stalk : X.Topos ⥤ Type u
  /-- the right adjoint `p_*` -/
  rightAdj : Type u ⥤ X.Topos
  /-- the adjunction `p^{-1} ⊣ p_*` -/
  adj : stalk ⊣ rightAdj
  /-- `p^{-1}` is left exact (preserves finite limits) -/
  preservesFiniteLimits : PreservesFiniteLimits stalk
  /-- `p^{-1}` preserves all colimits -/
  preservesColimits : PreservesColimits stalk
  /-- a lift of the stalk functor to sheaves of rings -/
  stalkRing : Sheaf X.J CommRingCat.{u} ⥤ CommRingCat.{u}
  /-- compatibility: forgetting the ring stalk agrees with the set stalk of the
      underlying sheaf of sets of `O` -/
  stalkRing_compat : stalkRing ⋙ forget CommRingCat.{u} ≅ X.OsetFunctor ⋙ stalk
  /-- the canonical identification `(O^*)_p ≅ (O_p)^*` (Stacks Lemma 18.40.11): the
      stalk of the units sheaf is the unit group of the stalk ring. -/
  stalkUnitsIso : X.unitsSheafFunctor ⋙ stalk ≅ stalkRing ⋙ unitsToType
  /-- compatibility axiom pinning down `stalkUnitsIso` as the canonical identification:
      it commutes with the unit inclusions, i.e. `(O^*)_p → (O_p)^* ↪ O_p` equals
      `(O^* ↪ O)_p`. -/
  stalkUnitsIso_compat : ∀ O : Sheaf X.J CommRingCat.{u},
    (stalkUnitsIso.app O).hom ≫ unitsIncl.app (stalkRing.obj O) ≫ (stalkRing_compat.app O).hom
      = stalk.map (X.unitsInclSheaf O)

attribute [instance] Point.preservesFiniteLimits
attribute [instance] Point.preservesColimits

namespace Point

variable {X : RingedTopos.{u}} (p : Point X)

/-- The stalk ring `O_{C,p} = (O_C)_p` of the structure sheaf at the point `p`. -/
noncomputable abbrev stalkRingObj : CommRingCat.{u} := p.stalkRing.obj X.O

end Point

/-- **Composite point** (Definition 4). Given a morphism of ringed topoi `f` and a
point `p` of `C`, the composite `q = f . p` is the point of `D` whose stalk functor is
`p^{-1} . f^{-1}`. Its ring-stalk lift is `finvRing . stalkRing_p`. This realizes
`(f^{-1} G)_p = G_q`; its `stalkUnitsIso` is assembled from `f.finvUnitsIso` and
`p.stalkUnitsIso`. -/
@[sga "4 IV 6.6" "partial"]
noncomputable def compositePoint {X Y : RingedTopos.{u}} (f : RingedToposHom X Y)
    (p : Point X) : Point Y where
  stalk := f.finv ⋙ p.stalk
  rightAdj := p.rightAdj ⋙ f.fdir
  adj := f.adj.comp p.adj
  preservesFiniteLimits := by
    have := f.invPreservesFiniteLimits
    have := p.preservesFiniteLimits
    exact CategoryTheory.Limits.comp_preservesFiniteLimits _ _
  preservesColimits := by
    have := f.invPreservesColimits
    have := p.preservesColimits
    infer_instance
  stalkRing := f.finvRing ⋙ p.stalkRing
  stalkRing_compat :=
    (Functor.associator f.finvRing p.stalkRing (forget CommRingCat.{u})) ≪≫
    Functor.isoWhiskerLeft f.finvRing p.stalkRing_compat ≪≫
    (Functor.associator f.finvRing X.OsetFunctor p.stalk).symm ≪≫
    Functor.isoWhiskerRight f.finvRing_compat p.stalk ≪≫
    (Functor.associator Y.OsetFunctor f.finv p.stalk)
  stalkUnitsIso :=
    (Functor.associator Y.unitsSheafFunctor f.finv p.stalk).symm ≪≫
    Functor.isoWhiskerRight f.finvUnitsIso p.stalk ≪≫
    (Functor.associator f.finvRing X.unitsSheafFunctor p.stalk) ≪≫
    Functor.isoWhiskerLeft f.finvRing p.stalkUnitsIso ≪≫
    (Functor.associator f.finvRing p.stalkRing unitsToType).symm
  stalkUnitsIso_compat := by
    intro O
    have hp := p.stalkUnitsIso_compat (f.finvRing.obj O)
    have key : p.stalk.map (f.finvUnitsIso.app O).hom ≫
        p.stalk.map (X.unitsInclSheaf (f.finvRing.obj O)) ≫
        p.stalk.map (f.finvRing_compat.app O).hom =
        p.stalk.map (f.finv.map (Y.unitsInclSheaf O)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, f.finvUnitsIso_compat O]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id, Category.assoc,
      Functor.comp_obj, Functor.comp_map]
    rw [← key, ← hp]
    simp only [Iso.app_hom, Category.assoc]

/-! ## The induced ring map on stalks -/

/-- Given `f`, a point `p` of `C` and `q = f . p`, taking the stalk at `p` of
`f^# : f^{-1} O_D -> O_C` produces a ring homomorphism `phi_p : O_{D,q} -> O_{C,p}`,
where `O_{D,q} = (compositePoint f p).stalkRingObj = p.stalkRing.obj (f.finvRing.obj O_D)`
and `O_{C,p} = p.stalkRingObj`. Concretely `phi_p = p.stalkRing.map f^#`. -/
noncomputable def stalkMap {X Y : RingedTopos.{u}} (f : RingedToposHom X Y)
    (p : Point X) :
    (compositePoint f p).stalkRingObj ⟶ p.stalkRingObj :=
  p.stalkRing.map f.fSharp

/-! ## Algebraic core (Definitions 2, 5, 8 at the level of sets).

For a ring homomorphism `phi : R -> S`, the square of unit inclusions
```
  Rˣ  --Units.map phi-->  Sˣ
  | (.)                    | (.)
  v                        v
  R   --------phi------->   S
```
is cartesian in `Sets` iff `phi` reflects units, i.e. `∀ a, IsUnit (phi a) ↔ IsUnit a`.
For local rings this is the local-ring-map condition (`IsLocalHom`). -/

/-- Cartesianness (Definition 5) of a square of sets
```
  A --t--> B
  |l       |r
  v        v
  C --b--> D
```
expressed as: the square commutes and the comparison map `A -> B ×_D C` is bijective. -/
structure IsCartesianSquareSet {A B C D : Type u}
    (t : A → B) (l : A → C) (r : B → D) (b : C → D) : Prop where
  /-- the square commutes -/
  comm : ∀ a, r (t a) = b (l a)
  /-- the comparison map to the fibre product is bijective -/
  bij : Function.Bijective
    (fun a : A => (⟨(t a, l a), comm a⟩ : {p : B × C // r p.1 = b p.2}))

/-- The unit-inclusion square of a ring homomorphism `phi : R -> S` (Definition 2 for
ordinary rings). Top map `Units.map phi`, bottom map `phi`, vertical maps the
coercions `Rˣ → R`, `Sˣ → S`. -/
def unitInclusionSquareCartesian {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) : Prop :=
  IsCartesianSquareSet
    (fun u : Rˣ => Units.map (φ : R →* S) u)
    (fun u : Rˣ => (u : R))
    (fun u : Sˣ => (u : S))
    (fun a : R => φ a)

/-- **Algebraic core, elementary form.** For any ring homomorphism `phi : R -> S`,
the unit-inclusion square is cartesian iff `phi` reflects units. -/
theorem unitInclusionSquareCartesian_iff_reflectsUnits
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    unitInclusionSquareCartesian φ ↔ ∀ a : R, IsUnit (φ a) ↔ IsUnit a := by
  unfold unitInclusionSquareCartesian
  constructor
  · intro hc a
    obtain ⟨comm, hinj, hsurj⟩ := hc
    constructor
    · intro ha
      obtain ⟨v, hv⟩ := ha
      obtain ⟨w, hw⟩ := hsurj ⟨(v, a), by simp [hv]⟩
      have hwa : ((w : R)) = a := congrArg (fun z => z.1.2) hw
      exact hwa ▸ Units.isUnit w
    · rintro ⟨u, rfl⟩
      exact (Units.map (φ : R →* S) u).isUnit
  · intro h
    refine ⟨fun u => by simp, ?_, ?_⟩
    · intro u1 u2 he
      have : ((u1 : R)) = (u2 : R) := congrArg (fun z => z.1.2) he
      exact Units.ext this
    · rintro ⟨⟨v, a⟩, (hva : (v : S) = φ a)⟩
      have : IsUnit a := (h a).1 (by rw [← hva]; exact v.isUnit)
      obtain ⟨u, rfl⟩ := this
      refine ⟨u, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Units.ext; exact hva.symm ▸ rfl
      · rfl

/-- **Algebraic core lemma** (Definitions 2, 8; the set-theoretic heart of part 3).
For a homomorphism of *local* rings `phi : R -> S`, the unit-inclusion square is
cartesian iff `phi` is a local ring map. -/
theorem unitInclusionSquareCartesian_iff_isLocalHom
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) :
    unitInclusionSquareCartesian φ ↔ IsLocalHom φ := by
  rw [unitInclusionSquareCartesian_iff_reflectsUnits]
  constructor
  · intro h; exact ⟨fun a ha => (h a).1 ha⟩
  · intro h a
    exact ⟨fun ha => IsLocalHom.map_nonunit a ha, fun ha => ha.map φ⟩

/-! ## Conditions (2) and (3) -/

/-- Condition (2): for every point `p` of `C`, with `q = f . p`, the square of *sets*
```
  O_{D,q}^*  -->  O_{C,p}^*
  | incl          | incl
  v               v
  O_{D,q}  --phi_p-> O_{C,p}
```
is cartesian. Here the corners are the stalks of the *units sheaves* and of the *ring
sheaves*: `O_{D,q}^* = (O_D^*)_q = stalk_q(O_D^*)`,
`O_{C,p}^* = (O_C^*)_p`, `O_{D,q} = (O_D)_q`, `O_{C,p} = (O_C)_p`. Concretely, using
`q^{-1} = p^{-1} . f^{-1}`, these are `p.stalk.obj (f.finv.obj Y.units)`,
`p.stalk.obj X.units`, `p.stalk.obj (f.finv.obj Y.Oset)`, `p.stalk.obj X.Oset`. The
vertical maps are `p^{-1}` of the unit inclusions, the bottom map is the stalk of
`f^#`, and the top map is the stalk of `f^#` on units. -/
def Condition2 {X Y : RingedTopos.{u}} (f : RingedToposHom X Y) : Prop :=
  ∀ p : Point X,
    IsPullback
      (p.stalk.map (f.fSharpUnits))
      (p.stalk.map (f.finv.map (Y.unitsInclSheaf Y.O)))
      (p.stalk.map (X.unitsInclSheaf X.O))
      (p.stalk.map (f.fSharpSet))

/-- **Condition (3)** (locally ringed case): for every point `p` of `C`, the induced
ring map `phi_p : O_{D,q} -> O_{C,p}` is a local ring map (Definition 8). -/
def Condition3 {X Y : RingedTopos.{u}} (f : RingedToposHom X Y) : Prop :=
  ∀ p : Point X, IsLocalHom (stalkMap f p).hom

/-! ## Conservative families and enough points (Definition 6). -/

/-- A *conservative family* of points of `(C, J)` (Definition 6): an index-set-indexed
family of points that detects isomorphisms of sheaves of sets. -/
structure ConservativeFamily (X : RingedTopos.{u}) where
  /-- index type -/
  ι : Type u
  /-- the points -/
  pt : ι → Point X
  /-- the family detects isomorphisms of sheaves of sets -/
  conservative : ∀ {F G : X.Topos} (η : F ⟶ G),
    IsIso η ↔ ∀ i, IsIso ((pt i).stalk.map η)

/-- A site *has enough points* (Definition 6) if it admits a conservative family. -/
@[sga "4 XVII 4.2.12" "(i)"]
def HasEnoughPoints (X : RingedTopos.{u}) : Prop :=
  Nonempty (ConservativeFamily X)

/-- **Condition (2)** restricted to a conservative family of points. -/
def Condition2OnFamily {X Y : RingedTopos.{u}} (f : RingedToposHom X Y)
    (P : ConservativeFamily X) : Prop :=
  ∀ i,
    IsPullback
      ((P.pt i).stalk.map (f.fSharpUnits))
      ((P.pt i).stalk.map (f.finv.map (Y.unitsInclSheaf Y.O)))
      ((P.pt i).stalk.map (X.unitsInclSheaf X.O))
      ((P.pt i).stalk.map (f.fSharpSet))

/-- **Condition (3)** restricted to a conservative family of points. -/
def Condition3OnFamily {X Y : RingedTopos.{u}} (f : RingedToposHom X Y)
    (P : ConservativeFamily X) : Prop :=
  ∀ i, IsLocalHom (stalkMap f (P.pt i)).hom

/-! ## Locally ringed topoi (Definition 7).

A ringed site `(C, O)` is a *locally ringed site* (Stacks Definition 18.40.4) if:
1. the canonical map `∅^# → Equalizer(0, 1 : * → O)` is an isomorphism; equivalently,
   whenever `U` is not sheaf-theoretically empty, the sections `0, 1 ∈ O(U)` are
   distinct. We formalize this equivalent sections-level form: an object `U` is
   *sheaf-theoretically empty* exactly when the empty sieve `⊥` is a covering of `U`
   (`(⊥ : Sieve U) ∈ J U`), so condition (1) reads: for every `U` with
   `(⊥ : Sieve U) ∉ J U`, one has `(0 : O(U)) ≠ 1`.
2. for every object `U` and every `f ∈ O(U)` there is a covering `{U_j -> U}` such
   that for each `j` either `f|_{U_j}` or `(1 - f)|_{U_j}` is invertible.

This is intrinsic to the ringed site (point-independent).

A standard consequence (Stacks Lemma 18.40, used in parts 3 and 4) is that for *every*
point `p` the stalk `O_{C,p}` is a local ring. Crucially this holds at each individual
point under the locally ringed hypothesis alone, with **no enough-points assumption**:
the local "unit or co-unit" condition is preserved by the exact stalk functor. We
therefore record it as a field `isLocalRing_stalk` of the structure, so that the
locally-ringed parts of the theorem need no `HasEnoughPoints` hypothesis. -/

/-- A section `f ∈ O(U)` is *locally a unit or a co-unit*: there is a covering
`{U_j -> U}` of `U` such that for each member of the covering, either the restriction
of `f` or the restriction of `1 - f` is a unit. (Condition 2 of Definition 7.) -/
def LocallyUnitOrCounit (X : RingedTopos.{u}) (U : X.C)
    (a : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (Opposite.op U) : CommRingCat.{u})) :
    Prop :=
  ∃ S : X.J.Cover U, ∀ ⦃V : X.C⦄ (g : V ⟶ U) (_ : S.1.arrows g),
    IsUnit (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).map g.op a) ∨
      IsUnit (1 - ((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).map g.op a)

/-- **Locally ringed ringed topos** (Definition 7), expressed intrinsically on the
structure sheaf:
* `nontrivial_on_nonempty` (condition (1)): on every object `U` that is not
  sheaf-theoretically empty — i.e. the empty sieve `⊥` does not cover `U` — the
  sections `0` and `1` of `O(U)` are distinct;
* `local_units` (condition (2)): every section is, locally on a covering, a unit or a
  co-unit;
* `isLocalRing_stalk` (standard consequence, Stacks Lemma 18.40): for *every* point
  `p`, the stalk `O_{C,p}` is a local ring. This holds at each individual point under
  the locally ringed hypothesis alone (no enough-points assumption), and is recorded
  as a field so the locally-ringed parts of the main theorem do not need any
  enough-points hypotheses. -/
structure IsLocallyRinged (X : RingedTopos.{u}) : Prop where
  /-- Condition 1 of Definition 7: on every object not sheaf-theoretically empty
      (the empty sieve does not cover it), `0 ≠ 1` in the sections. -/
  nontrivial_on_nonempty : ∀ U : X.C, (⊥ : Sieve U) ∉ X.J U →
    (0 : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (Opposite.op U) : CommRingCat.{u})) ≠
        1
  /-- Condition 2 of Definition 7: every section of `O` is, on some covering, a unit
      or a co-unit. -/
  local_units : ∀ (U : X.C)
      (a : (((sheafToPresheaf X.J CommRingCat.{u}).obj X.O).obj (Opposite.op U) : CommRingCat.{u})),
    LocallyUnitOrCounit X U a
  /-- Standard consequence (Stacks Lemma 18.40): every stalk is a local ring. Holds at
      each individual point under the locally ringed hypothesis alone, with no
      enough-points assumption. -/
  isLocalRing_stalk : ∀ p : Point X, IsLocalRing p.stalkRingObj

/-! ## Main Statements

The theorem (Stacks Tag 04H9, Lemma 18.40.8) consists of the implications below. -/

variable {X Y : RingedTopos.{u}}

/-- **Theorem, part 1: (1) ⇒ (2) always holds** (no hypotheses beyond Definition 1).

Each stalk functor `(.)_p = p^{-1}` is exact, hence preserves the cartesian square of
condition (1); together with the identifications `(f^{-1} O_D)_p = O_{D,q}` and
`(f^{-1} O_D^*)_p = O_{D,q}^*`, this yields condition (2). -/
@[stacks 04H9 "(1)⇒(2)", sga "4 IV 13.9" "c) (i) => (ii)"]
theorem condition1_imp_condition2 (f : RingedToposHom X Y)
    (h : Condition1 f) : Condition2 f := by
  -- SKETCH: `Condition2 f` at `p` is literally `Condition1 f` pushed through the exact
  -- stalk functor `p.stalk`. Since `p.stalk` preserves finite limits
  -- (`p.preservesFiniteLimits`, an instance), it preserves the cospan pullback, so
  -- `IsPullback.map p.stalk` applies. The four mapped arrows are definitionally the
  -- four arrows in `Condition2 f p`.
  -- DIRECTLY CLOSABLE: `intro p; exact h.map p.stalk` (the `PreservesLimit (cospan ..)`
  -- instance is found from `Point.preservesFiniteLimits`).
  intro p
  exact h.map p.stalk

/-- **Theorem, part 4 (general case): (2) on a conservative family implies (1).**

If condition (2) holds for every point of a conservative family of points of `C`, then
condition (1) holds (the family detects cartesianness of the sheaf square). -/
@[stacks 04H9 "(2)-family⇒(1)", sga "4 IV 13.9" "c) (ii)⇒(i) conserv fam"]
theorem condition1_of_condition2OnFamily (f : RingedToposHom X Y)
    (P : ConservativeFamily X) (h : Condition2OnFamily f P) :
    Condition1 f := by
  -- SKETCH: `Condition1 f` is the sheaf square being a pullback; `Condition2OnFamily f P`
  -- gives that its image under every `(P.pt i).stalk` is a pullback. The reflection
  -- argument (a jointly-conservative family of finite-limit-preserving functors reflects
  -- pullbacks) is inlined here as a local `have` (no new top-level declaration), then
  -- applied to the four maps of the units-sheaf square.
  have isPullback_of_conservativeFamily :
      ∀ {A B C D : X.Topos} (t : A ⟶ B) (l : A ⟶ C) (r : B ⟶ D) (b : C ⟶ D),
        (∀ i, IsPullback ((P.pt i).stalk.map t) ((P.pt i).stalk.map l)
          ((P.pt i).stalk.map r) ((P.pt i).stalk.map b)) →
        IsPullback t l r b := by
    intro A B C D t l r b hsq
    -- Joint faithfulness: a conservative finite-limit-preserving family detects equality
    -- of parallel maps via the equalizer trick.
    have jointlyFaithful : ∀ {F G : X.Topos} (g h : F ⟶ G),
        (∀ i, (P.pt i).stalk.map g = (P.pt i).stalk.map h) → g = h := by
      intro F G g h hgh
      have hiso : IsIso (equalizer.ι g h) := by
        rw [P.conservative]
        intro i
        have hcomp : equalizerComparison g h (P.pt i).stalk
            ≫ equalizer.ι ((P.pt i).stalk.map g) ((P.pt i).stalk.map h)
            = (P.pt i).stalk.map (equalizer.ι g h) := equalizerComparison_comp_π g h _
        have _hι : IsIso (equalizer.ι ((P.pt i).stalk.map g) ((P.pt i).stalk.map h)) :=
          equalizer.ι_of_eq (hgh i)
        have _hcomp_iso : IsIso (equalizerComparison g h (P.pt i).stalk) := by
          rw [← PreservesEqualizer.iso_hom]; infer_instance
        rw [← hcomp]; infer_instance
      have hcond : equalizer.ι g h ≫ g = equalizer.ι g h ≫ h := equalizer.condition g h
      exact (cancel_epi (equalizer.ι g h)).mp hcond
    -- Step 1: commutativity, via joint faithfulness of the conservative family.
    have w : t ≫ r = l ≫ b := by
      apply jointlyFaithful
      intro i
      simp only [Functor.map_comp]
      exact (hsq i).w
    -- Step 2: the comparison map into the actual pullback is a stalkwise iso, hence an iso.
    set Pb := Limits.pullback r b with hPb
    set c : A ⟶ Pb := pullback.lift t l w with hc
    have hciso : IsIso c := by
      rw [P.conservative]
      intro i
      let S := (P.pt i).stalk
      have key : S.map c ≫ (PreservesPullback.iso S r b).hom = (hsq i).isoPullback.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← S.map_comp,
            pullback.lift_fst, (hsq i).isoPullback_hom_fst]
        · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← S.map_comp,
            pullback.lift_snd, (hsq i).isoPullback_hom_snd]
      have : IsIso (S.map c ≫ (PreservesPullback.iso S r b).hom) := by
        rw [key]; infer_instance
      exact IsIso.of_isIso_comp_right (S.map c) (PreservesPullback.iso S r b).hom
    -- Step 3: conclude.
    refine IsPullback.of_iso_pullback ⟨w⟩ (asIso c) ?_ ?_
    · simp only [asIso_hom, hc, pullback.lift_fst]
    · simp only [asIso_hom, hc, pullback.lift_snd]
  exact isPullback_of_conservativeFamily
    (f.fSharpUnits) (f.finv.map (Y.unitsInclSheaf Y.O))
    (X.unitsInclSheaf X.O) (f.fSharpSet) h

/-- **Theorem, part 2: if `C` has enough points, then (1) ⇔ (2).**

Forward is part 1. Conversely a conservative family of points detects whether a square
of sheaves is cartesian (cartesianness is preserved and reflected by the exact,
jointly-conservative stalk functors), so condition (2) forces condition (1). -/
@[stacks 04H9 "(1)⇔(2)", sga "4 IV 13.9" "c) (i) <=> (ii)"]
theorem condition1_iff_condition2_of_enoughPoints (f : RingedToposHom X Y)
    (hC : HasEnoughPoints X) :
    Condition1 f ↔ Condition2 f := by
  obtain ⟨P⟩ := hC
  constructor
  · exact condition1_imp_condition2 f
  · intro h2
    exact condition1_of_condition2OnFamily f P (fun i => h2 (P.pt i))

/-- At a point `p`, with both stalk rings local, the stalk square of condition (2) is
cartesian iff the stalk map `phi_p` is a local ring map. -/
private theorem isPullback_stalk_iff_isLocalHom (f : RingedToposHom X Y)
    (hlrC : IsLocallyRinged X) (hlrD : IsLocallyRinged Y) (p : Point X) :
    IsPullback
      (p.stalk.map (f.fSharpUnits))
      (p.stalk.map (f.finv.map (Y.unitsInclSheaf Y.O)))
      (p.stalk.map (X.unitsInclSheaf X.O))
      (p.stalk.map (f.fSharpSet)) ↔ IsLocalHom (stalkMap f p).hom := by
  -- Inlined helper_04h9: `IsPullback ↔ IsCartesianSquareSet` in `Type u`.
  have isPullback_iff : ∀ {A B C D : Type u} (t : A ⟶ B) (l : A ⟶ C) (r : B ⟶ D)
      (b : C ⟶ D), IsPullback t l r b ↔ IsCartesianSquareSet t l r b := by
    intro A B C D t l r b
    constructor
    · intro h
      have comm : ∀ a, r (t a) = b (l a) := by
        intro a
        have hw := h.w
        rw [← types_comp_apply t r, ← types_comp_apply l b, hw]
      refine ⟨comm, ?_⟩
      let j : A ≅ Types.PullbackObj r b := h.isoPullback ≪≫ Types.pullbackIsoPullback r b
      have hfst : ∀ a : A,
          ((ConcreteCategory.hom j.hom a : Types.PullbackObj r b) : B × C).1 = t a := by
        intro a
        change ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a) : B × C).1 = t a
        have key : pullback.fst r b ((Types.pullbackIsoPullback r b).inv
            ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a)))
            = ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a) : B × C).1 := by
          rw [← types_comp_apply ((Types.pullbackIsoPullback r b).inv) (pullback.fst r b),
            Types.pullbackIsoPullback_inv_fst]; rfl
        rw [Iso.hom_inv_id_apply] at key
        rw [← key, ← types_comp_apply (h.isoPullback.hom) (pullback.fst r b),
          h.isoPullback_hom_fst]
      have hsnd : ∀ a : A,
          ((ConcreteCategory.hom j.hom a : Types.PullbackObj r b) : B × C).2 = l a := by
        intro a
        change ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a) : B × C).2 = l a
        have key : pullback.snd r b ((Types.pullbackIsoPullback r b).inv
            ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a)))
            = ((Types.pullbackIsoPullback r b).hom (h.isoPullback.hom a) : B × C).2 := by
          rw [← types_comp_apply ((Types.pullbackIsoPullback r b).inv) (pullback.snd r b),
            Types.pullbackIsoPullback_inv_snd]; rfl
        rw [Iso.hom_inv_id_apply] at key
        rw [← key, ← types_comp_apply (h.isoPullback.hom) (pullback.snd r b),
          h.isoPullback_hom_snd]
      have hcmp : (fun a : A => (⟨(t a, l a), comm a⟩ : Types.PullbackObj r b))
          = ConcreteCategory.hom j.hom := by
        funext a
        apply Subtype.ext
        apply Prod.ext
        · exact (hfst a).symm
        · exact (hsnd a).symm
      rw [hcmp]
      exact ConcreteCategory.bijective_of_isIso j.hom
    · intro h
      obtain ⟨comm, hbij⟩ := h
      set cmp : A → Types.PullbackObj r b := fun a => ⟨(t a, l a), comm a⟩ with hcmp
      let e : A ≃ Types.PullbackObj r b := Equiv.ofBijective cmp hbij
      let i : A ≅ Limits.pullback r b := e.toIso ≪≫ (Types.pullbackIsoPullback r b).symm
      have hw : CommSq t l r b := by
        constructor
        apply ConcreteCategory.hom_ext
        intro a
        simp only [types_comp_apply]
        exact comm a
      have hihom : ∀ a : A, i.hom a = (Types.pullbackIsoPullback r b).inv (cmp a) := by
        intro a
        change (Types.pullbackIsoPullback r b).inv (ConcreteCategory.hom e.toIso.hom a) = _
        rw [Equiv.toIso_hom_hom_apply, Equiv.ofBijective_apply]
      refine IsPullback.of_iso_pullback hw i ?_ ?_
      · apply ConcreteCategory.hom_ext
        intro a
        rw [types_comp_apply, hihom, ← types_comp_apply, Types.pullbackIsoPullback_inv_fst]
        rfl
      · apply ConcreteCategory.hom_ext
        intro a
        rw [types_comp_apply, hihom, ← types_comp_apply, Types.pullbackIsoPullback_inv_snd]
        rfl
  -- Inlined helper_04h9: transport `IsCartesianSquareSet` along corner bijections.
  have transport : ∀ {A B C D A' B' C' D' : Type u}
      (t : A → B) (l : A → C) (r : B → D) (b : C → D)
      (t' : A' → B') (l' : A' → C') (r' : B' → D') (b' : C' → D')
      (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C') (eD : D ≃ D')
      (_ : ∀ a, t' (eA a) = eB (t a))
      (_ : ∀ a, l' (eA a) = eC (l a))
      (_ : ∀ x, r' (eB x) = eD (r x))
      (_ : ∀ x, b' (eC x) = eD (b x))
      (_ : IsCartesianSquareSet t l r b),
      IsCartesianSquareSet t' l' r' b' := by
    intro A B C D A' B' C' D' t l r b t' l' r' b' eA eB eC eD htop hleft hright hbot h
    obtain ⟨comm, hbij⟩ := h
    have comm' : ∀ a' : A', r' (t' a') = b' (l' a') := by
      intro a'
      have := comm (eA.symm a')
      rw [← eA.apply_symm_apply a', htop, hleft, hright, hbot, this]
    refine ⟨comm', ?_⟩
    let efib : {p : B × C // r p.1 = b p.2} ≃ {p : B' × C' // r' p.1 = b' p.2} :=
      ⟨fun q => ⟨(eB q.1.1, eC q.1.2), by rw [hright, hbot]; exact congrArg eD q.2⟩,
       fun q => ⟨(eB.symm q.1.1, eC.symm q.1.2), by
          apply eD.injective
          rw [← hright, ← hbot, eB.apply_symm_apply, eC.apply_symm_apply]; exact q.2⟩,
       fun q => by apply Subtype.ext; apply Prod.ext <;> simp,
       fun q => by apply Subtype.ext; apply Prod.ext <;> simp⟩
    have key : (fun a' : A' => (⟨(t' a', l' a'), comm' a'⟩ : {p : B' × C' // r' p.1 = b' p.2}))
        = efib ∘ (fun a : A => (⟨(t a, l a), comm a⟩ : {p : B × C // r p.1 = b
            p.2})) ∘ eA.symm := by
      funext a'
      simp only [Function.comp_apply]
      apply Subtype.ext
      change (t' a', l' a') = (eB (t (eA.symm a')), eC (l (eA.symm a')))
      apply Prod.ext
      · change t' a' = eB (t (eA.symm a'))
        rw [← htop, eA.apply_symm_apply]
      · change l' a' = eC (l (eA.symm a'))
        rw [← hleft, eA.apply_symm_apply]
    rw [key]
    exact efib.bijective.comp (hbij.comp eA.symm.bijective)
  have _hC : IsLocalRing (p.stalkRingObj) := hlrC.isLocalRing_stalk p
  have _hD : IsLocalRing ((compositePoint f p).stalkRingObj) :=
    hlrD.isLocalRing_stalk (compositePoint f p)
  rw [← unitInclusionSquareCartesian_iff_isLocalHom, isPullback_iff]
  -- the composite point q = f ∘ p, with stalk ring O_{D,q}
  set q := compositePoint f p with hq
  -- four corner equivalences via the data isos
  let eA := (q.stalkUnitsIso.app Y.O).toEquiv
  let eB := (p.stalkUnitsIso.app X.O).toEquiv
  let eC := (q.stalkRing_compat.app Y.O).symm.toEquiv
  let eD := (p.stalkRing_compat.app X.O).symm.toEquiv
  -- the four naturality / compatibility relations, proven once at the morphism level
  have hleft : ∀ a, (q.stalkRing_compat.app Y.O).hom
        (((q.stalkUnitsIso.app Y.O).hom a).val)
      = q.stalk.map (Y.unitsInclSheaf Y.O) a := by
    intro a
    have := congrArg (fun φ : (Y.unitsSheafFunctor ⋙ q.stalk).obj Y.O ⟶
        (Y.OsetFunctor ⋙ q.stalk).obj Y.O => ConcreteCategory.hom φ a)
      (q.stalkUnitsIso_compat Y.O)
    simp only [types_comp_apply] at this
    exact this
  have hright : ∀ x, (p.stalkRing_compat.app X.O).hom
        (((p.stalkUnitsIso.app X.O).hom x).val)
      = p.stalk.map (X.unitsInclSheaf X.O) x := by
    intro x
    have := congrArg (fun φ : (X.unitsSheafFunctor ⋙ p.stalk).obj X.O ⟶
        (X.OsetFunctor ⋙ p.stalk).obj X.O => ConcreteCategory.hom φ x)
      (p.stalkUnitsIso_compat X.O)
    simp only [types_comp_apply] at this
    exact this
  have htop : ∀ a, (Units.map (stalkMap f p).hom.toMonoidHom) (eA a) =
      eB (ConcreteCategory.hom (p.stalk.map f.fSharpUnits) a) := by
    have hQ : (q.stalkUnitsIso.app Y.O).hom
        = p.stalk.map (f.finvUnitsIso.app Y.O).hom ≫
            (p.stalkUnitsIso.app (f.finvRing.obj Y.O)).hom := by
      change ((compositePoint f p).stalkUnitsIso.app Y.O).hom = _
      simp [compositePoint]
    have hM : (q.stalkUnitsIso.app Y.O).hom ≫
          (p.stalkRing ⋙ unitsToType).map f.fSharp
        = p.stalk.map f.fSharpUnits ≫ (p.stalkUnitsIso.app X.O).hom := by
      have hnat := p.stalkUnitsIso.hom.naturality f.fSharp
      simp only [Functor.comp_map, ← Iso.app_hom] at hnat
      rw [hQ, RingedToposHom.fSharpUnits, Functor.map_comp, Category.assoc]
      simp only [Functor.comp_map]
      rw [← hnat, ← Category.assoc]
    intro a
    have key := congrArg (fun φ : (Y.unitsSheafFunctor ⋙ q.stalk).obj Y.O ⟶
        (p.stalkRing ⋙ unitsToType).obj X.O => ConcreteCategory.hom φ a) hM
    simp only [types_comp_apply] at key
    exact key
  have hbot : ∀ x, (stalkMap f p).hom (eC x) =
      eD (ConcreteCategory.hom (p.stalk.map f.fSharpSet) x) := by
    have hQ : (q.stalkRing_compat.app Y.O).hom
        = (p.stalkRing_compat.app (f.finvRing.obj Y.O)).hom ≫
            p.stalk.map (f.finvRing_compat.app Y.O).hom := by
      change ((compositePoint f p).stalkRing_compat.app Y.O).hom = _
      simp [compositePoint]
    have hcancel : p.stalk.map (f.finvRing_compat.app Y.O).hom ≫
          p.stalk.map (f.finvRing_compat.symm.app Y.O).hom = 𝟙 _ := by
      rw [← p.stalk.map_comp]; simp
    have hM : (p.stalkRing ⋙ forget CommRingCat.{u}).map f.fSharp ≫
          (p.stalkRing_compat.app X.O).hom
        = (q.stalkRing_compat.app Y.O).hom ≫ p.stalk.map f.fSharpSet := by
      have hnat := p.stalkRing_compat.hom.naturality f.fSharp
      rw [hQ, RingedToposHom.fSharpSet, Functor.map_comp, Category.assoc,
        ← Category.assoc (p.stalk.map (f.finvRing_compat.app Y.O).hom), hcancel,
        Category.id_comp]
      simpa only [Functor.comp_map, Iso.app_hom] using hnat
    intro x
    have key := congrArg (fun φ : (p.stalkRing ⋙ forget CommRingCat.{u}).obj
        (f.finvRing.obj Y.O) ⟶ (X.OsetFunctor ⋙ p.stalk).obj X.O =>
      ConcreteCategory.hom φ ((q.stalkRing_compat.app Y.O).inv x)) hM
    simp only [types_comp_apply] at key
    change ConcreteCategory.hom ((p.stalkRing ⋙ forget CommRingCat.{u}).map f.fSharp)
          ((q.stalkRing_compat.app Y.O).inv x)
        = (p.stalkRing_compat.app X.O).inv (ConcreteCategory.hom (p.stalk.map f.fSharpSet) x)
    apply (ConcreteCategory.bijective_of_isIso (p.stalkRing_compat.app X.O).hom).injective
    rw [Iso.inv_hom_id_apply, key]
    congr 1
    exact (q.stalkRing_compat.app Y.O).inv_hom_id_apply x
  -- helper_04h9 defeqs for the corner equivs
  have heC : ∀ y, eC y = (q.stalkRing_compat.app Y.O).inv y := fun _ => rfl
  have heD : ∀ y, eD y = (p.stalkRing_compat.app X.O).inv y := fun _ => rfl
  have heA : ∀ a, eA a = (q.stalkUnitsIso.app Y.O).hom a := fun _ => rfl
  have heB : ∀ x, eB x = (p.stalkUnitsIso.app X.O).hom x := fun _ => rfl
  -- vertical relations in transport's form (l'/r' become Units.val)
  have hLV : ∀ a, (eA a).val = eC (q.stalk.map (Y.unitsInclSheaf Y.O) a) := by
    intro a
    rw [heA, heC, ← hleft a, Iso.hom_inv_id_apply]
  have hRV : ∀ x, (eB x).val = eD (p.stalk.map (X.unitsInclSheaf X.O) x) := by
    intro x
    rw [heB, heD, ← hright x, Iso.hom_inv_id_apply]
  constructor
  · intro h
    exact transport _ _ _ _ _ _ _ _ eA eB eC eD htop hLV hRV hbot h
  · intro h
    refine transport _ _ _ _ _ _ _ _
      eA.symm eB.symm eC.symm eD.symm ?_ ?_ ?_ ?_ h
    · intro a
      rw [Equiv.eq_symm_apply]
      have := htop (eA.symm a)
      rw [eA.apply_symm_apply] at this
      exact this.symm
    · intro a
      rw [Equiv.eq_symm_apply]
      have := hLV (eA.symm a)
      rw [eA.apply_symm_apply] at this
      exact this.symm
    · intro x
      rw [Equiv.eq_symm_apply]
      have := hRV (eB.symm x)
      rw [eB.apply_symm_apply] at this
      exact this.symm
    · intro x
      rw [Equiv.eq_symm_apply]
      have := hbot (eC.symm x)
      rw [eC.apply_symm_apply] at this
      exact this.symm

/-- **Theorem, part 3: in the locally ringed case, (2) ⇔ (3).**

When both topoi are locally ringed, every stalk `O_{C,p}` and `O_{D,q}` is a local ring
(via `IsLocallyRinged.isLocalRing_stalk`, with no enough-points assumption on either
`C` or `D`), so condition (2) at `p` — the cartesianness of the stalk-of-units-sheaves
square — is, via the identifications `(O^*)_p = (O_p)^*` (`stalkUnitsIso`), exactly the
statement that the unit-inclusion square of `phi_p` is cartesian, which by the
algebraic core lemma is equivalent to `phi_p` being a local ring map. -/
@[stacks 04H9 "(2)⇔(3)"]
theorem condition2_iff_condition3_of_locallyRinged (f : RingedToposHom X Y)
    (hlrC : IsLocallyRinged X) (hlrD : IsLocallyRinged Y) :
    Condition2 f ↔ Condition3 f := by
  constructor
  · intro h2 p
    exact (isPullback_stalk_iff_isLocalHom f hlrC hlrD p).1 (h2 p)
  · intro h3 p
    exact (isPullback_stalk_iff_isLocalHom f hlrC hlrD p).2 (h3 p)

/-- **Theorem, part 4 (locally ringed case): (3) on a conservative family implies (1).**

If both topoi are locally ringed and `phi_p` is a local ring map for every point `p` of
a conservative family of points of `C`, then condition (1) holds. No enough-points
assumption on `D` is needed. -/
@[stacks 04H9 "(3)-family⇒(1)", sga "4 IV 13.9" "c) (ii)⇒(i) conserv fam"]
theorem condition1_of_condition3OnFamily_of_locallyRinged (f : RingedToposHom X Y)
    (hlrC : IsLocallyRinged X) (hlrD : IsLocallyRinged Y)
    (P : ConservativeFamily X) (h : Condition3OnFamily f P) :
    Condition1 f := by
  exact condition1_of_condition2OnFamily f P fun i =>
    (isPullback_stalk_iff_isLocalHom f hlrC hlrD (P.pt i)).2 (h i)

end Stacks.Sheaves.LocallyRingedTopos
