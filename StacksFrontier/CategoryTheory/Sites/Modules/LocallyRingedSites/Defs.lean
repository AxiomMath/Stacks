module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksCore.CategoryTheory.Sites.Point.StalkAsColimit
public import StacksCore.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.EmptySheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.LocalUnitConditions
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily
public import StacksFrontier.CategoryTheory.Sites.Point.StalkPreservesFiniteLimits

/-!
# Locally ringed sites

A ringed site `(C, J, O)` is *locally ringed* when two conditions hold: the sections `0` and
`1` of the structure sheaf are nowhere equal, and every section of the structure sheaf is,
after passing to a covering, either a unit or has unit complement.

The first condition is the one of Stacks 05D7: it is expressed by the canonical morphism from
the empty sheaf to the equalizer of the zero and one sections being an isomorphism. The second
is the first of the three equivalent local-unit criteria of Stacks 04ES, here stated with the
universe of the sections independent of the site's.

The local unit-or-unit-complement condition forces every stalk of the structure sheaf to be
either the zero ring or a local ring, and on a site with a conservative family of points the
converse holds. On such a site the sections `0` and `1` are nowhere equal exactly when every
stalk of the structure sheaf is a nonzero ring.

## Main definitions

* `AlgebraicGeometry.RingedSite.LocallyUnitOrOneSubUnit`: the local unit-or-unit-complement
  condition on sections of the structure sheaf, for a ringed site whose universes all agree.
* `AlgebraicGeometry.RingedSite.StalksAreZeroOrLocal`: every stalk is the zero ring or a local
  ring.
* `AlgebraicGeometry.RingedSite.underlyingStructureSheaf`, `zeroSection`, `oneSection`: the
  underlying sheaf of sets of the structure sheaf and its two distinguished global sections.
* `AlgebraicGeometry.RingedSite.oneIsNeverZero`: the canonical map from the empty sheaf to the
  equalizer of the zero and one sections.
* `AlgebraicGeometry.RingedSite.LocallyEitherUnit`: every section of a sheaf of commutative
  rings is locally either a unit or has unit complement.
* `AlgebraicGeometry.RingedSite.IsLocallyRinged`: the locally ringed site predicate.

## Main results

* `AlgebraicGeometry.RingedSite.stalksAreZeroOrLocal_of_locallyUnitOrOneSubUnit`: the local
  unit-or-unit-complement condition makes every stalk zero or local.
* `AlgebraicGeometry.RingedSite.locallyUnitOrOneSubUnit_iff_stalksAreZeroOrLocal`: the
  equivalence on a site with a conservative family of points.
* `AlgebraicGeometry.RingedSite.locallyUnitOrOneSubUnit_iff_locallyEitherUnit`: on a ringed
  site whose universes all agree, `LocallyEitherUnit` is equivalent to
  `LocallyUnitOrOneSubUnit`.
* `AlgebraicGeometry.RingedSite.isIso_oneIsNeverZero_iff_forall_nontrivial_stalk`: on a site
  with a conservative family of points, `0` and `1` are nowhere equal exactly when every stalk
  of the structure sheaf is a nonzero ring.
* `AlgebraicGeometry.RingedSite.locallyEitherUnit_of_local_stalks` and
  `AlgebraicGeometry.RingedSite.isLocallyRinged_of_local_stalks`: the stalk criterion for local
  ringedness. A ringed site is locally ringed as soon as the stalk of its structure sheaf is a
  local ring at every point of *one* conservative family of points.

## Implementation notes

`IsLocallyRinged` is an abbreviation, so that a client can use either conjunct directly
without a conversion lemma. The site's objects, the site's morphisms and the rings of sections
have independent universes; `AlgebraicGeometry.RingedSite.LocallyUnitOrOneSubUnit` is the
special case in which they coincide, up to moving the restriction map across the subtraction.

A covering family is represented by its generated covering sieve; equivalently, the local
condition asks for a covering sieve all of whose arrows have the required property. The
zero-ring alternative for a stalk is expressed by `Subsingleton`, because Mathlib's
`IsLocalRing` includes nontriviality.

The singleton sheaf is Mathlib's `CategoryTheory.Sheaf.terminal` on `PUnit`, and the empty
sheaf is the chosen initial object of the category of sheaves of sets; the latter is supported
on exactly the objects covered by the empty sieve, so no sheafification and no size relation
between the site and the sections is needed.

## References

* [Stacks Project, Tag 04ET](https://stacks.math.columbia.edu/tag/04ET)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 05D7](https://stacks.math.columbia.edu/tag/05D7)
* [Stacks Project, Tag 05D8](https://stacks.math.columbia.edu/tag/05D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w'

namespace AlgebraicGeometry.RingedSite

/-! ### Stalks of a locally ringed site -/

/-- Over a point, a section whose germ is a unit becomes a unit on a neighbourhood. -/
private theorem point_exists_unit_restriction (X : RingedSite.{v, u, u})
    (p : X.J.Point.{u}) (U : X.C) (x : p.fiber.obj U)
    (a : X.O.obj.obj (Opposite.op U))
    (ha : IsUnit (p.toPresheafFiber U x X.O.obj a)) :
    ∃ (V : X.C) (f : V ⟶ U) (y : p.fiber.obj V),
      p.fiber.map f y = x ∧ IsUnit (X.O.obj.map f.op a) := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨V, y, b, hb⟩ :=
    p.toPresheafFiber_jointly_surjective (P := X.O.obj) (↑w⁻¹)
  let e₁ : p.fiber.Elements := p.fiber.elementsMk U x
  let e₂ : p.fiber.Elements := p.fiber.elementsMk V y
  obtain ⟨e, α, β, _⟩ := IsCofilteredOrEmpty.cone_objs e₁ e₂
  rcases e with @⟨W, z⟩
  let f : W ⟶ U := α.hom
  let g : W ⟶ V := β.hom
  have hf : p.fiber.map f z = x := α.map_val
  have hg : p.fiber.map g z = y := β.map_val
  have haW : p.toPresheafFiber W z X.O.obj (X.O.obj.map f.op a) =
      p.toPresheafFiber U x X.O.obj a := by
    rw [← hf]
    exact p.toPresheafFiber_w_apply f z X.O.obj a
  have hbW : p.toPresheafFiber W z X.O.obj (X.O.obj.map g.op b) =
      p.toPresheafFiber V y X.O.obj b := by
    rw [← hg]
    exact p.toPresheafFiber_w_apply g z X.O.obj b
  have hprod : p.toPresheafFiber W z X.O.obj
      (X.O.obj.map f.op a * X.O.obj.map g.op b) =
      p.toPresheafFiber W z X.O.obj 1 := by
    rw [map_mul, haW, hbW, ← hw, hb]
    simp
  obtain ⟨W', k, z', hkz, hprod'⟩ :=
    (p.toPresheafFiber_eq_iff' W z
      (X.O.obj.map f.op a * X.O.obj.map g.op b) 1).mp hprod
  have hmul : X.O.obj.map (k ≫ f).op a * X.O.obj.map (k ≫ g).op b = 1 := by
    simpa [Functor.map_comp, map_mul, map_one] using hprod'
  have hunit : IsUnit (X.O.obj.map (k ≫ f).op a) :=
    IsUnit.of_mul_eq_one_right (X.O.obj.map (k ≫ g).op b) (by
      simpa only [mul_comm] using hmul)
  refine ⟨W', k ≫ f, z', ?_, hunit⟩
  calc
    p.fiber.map (k ≫ f) z' = p.fiber.map f (p.fiber.map k z') := by simp
    _ = x := by rw [hkz, hf]

/-- Over a point, a section whose germ is a unit or has unit complement is, on a neighbourhood,
a unit or has unit complement. -/
private theorem point_exists_unit_or_one_sub_unit_restriction (X : RingedSite.{v, u, u})
    (p : X.J.Point.{u}) (U : X.C) (x : p.fiber.obj U)
    (a : X.O.obj.obj (Opposite.op U))
    (ha : IsUnit (p.toPresheafFiber U x X.O.obj a) ∨
      IsUnit (1 - p.toPresheafFiber U x X.O.obj a)) :
    ∃ (V : X.C) (f : V ⟶ U) (y : p.fiber.obj V),
      p.fiber.map f y = x ∧
        (IsUnit (X.O.obj.map f.op a) ∨ IsUnit (1 - X.O.obj.map f.op a)) := by
  rcases ha with ha | ha
  · obtain ⟨V, f, y, hy, hu⟩ := point_exists_unit_restriction X p U x a ha
    exact ⟨V, f, y, hy, Or.inl hu⟩
  · obtain ⟨V, f, y, hy, hu⟩ := point_exists_unit_restriction X p U x (1 - a)
      (by simpa only [map_sub, map_one] using ha)
    exact ⟨V, f, y, hy, Or.inr (by simpa only [map_sub, map_one] using hu)⟩

/-- Every section of the structure sheaf is locally either a unit or has unit
complement. -/
def LocallyUnitOrOneSubUnit (X : RingedSite.{u, u, u}) : Prop :=
  ∀ (U : X.C) (a : X.O.obj.obj (Opposite.op U)),
    ∃ S : Sieve U, S ∈ X.J U ∧
      (∀ (V : X.C) (f : V ⟶ U), S f →
        (IsUnit (X.O.obj.map f.op a) ∨ IsUnit (1 - X.O.obj.map f.op a)))

/-- Every stalk of the structure sheaf is either the zero ring or a local ring. -/
def StalksAreZeroOrLocal (X : RingedSite.{u, u, u}) : Prop :=
  ∀ p : X.J.Point.{u},
    Subsingleton ((p.sheafFiber (A := CommRingCat.{u})).obj X.O) ∨
      IsLocalRing ((p.sheafFiber (A := CommRingCat.{u})).obj X.O)

/-- The local unit-or-unit-complement condition makes every stalk of the structure sheaf either
the zero ring or a local ring. -/
@[stacks 04ET "(1) implies (2)", sga "4 IV 13.9" "b) (iii) => (iv)"]
theorem stalksAreZeroOrLocal_of_locallyUnitOrOneSubUnit (X : RingedSite.{u, u, u})
    (h : LocallyUnitOrOneSubUnit X) : StalksAreZeroOrLocal X := by
  intro p
  let R := p.presheafFiber.obj X.O.obj
  let S := (p.sheafFiber (A := CommRingCat.{u})).obj X.O
  let : CommRing R := inferInstance
  let : CommRing S := inferInstance
  let e : R ≃+* S :=
    (p.sheafToPresheafCompPresheafFiberIso.app X.O).commRingCatIsoToRingEquiv
  have hR : Subsingleton R ∨ IsLocalRing R := by
    by_cases hR : Subsingleton R
    · exact Or.inl hR
    · right
      let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
      intro a
      obtain ⟨U, x, b, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := X.O.obj) a
      obtain ⟨T, hT, hTprop⟩ := h U b
      obtain ⟨V, g, hg, y, hy⟩ := p.jointly_surjective T hT x
      have hloc := hTprop V g hg
      have hsame : p.toPresheafFiber V y X.O.obj (X.O.obj.map g.op b) =
          p.toPresheafFiber U x X.O.obj b := by
        rw [← hy]
        exact p.toPresheafFiber_w_apply g y X.O.obj b
      rcases hloc with hf | hf
      · left
        rw [← hsame]
        exact hf.map (ConcreteCategory.hom (p.toPresheafFiber V y X.O.obj))
      · right
        have hcomp : p.toPresheafFiber V y X.O.obj
            (1 - X.O.obj.map g.op b) = 1 - p.toPresheafFiber U x X.O.obj b := by
          rw [map_sub, map_one, hsame]
        rw [← hcomp]
        exact hf.map (ConcreteCategory.hom (p.toPresheafFiber V y X.O.obj))
  rcases hR with hzero | hlocal
  · exact Or.inl (e.toEquiv.subsingleton_congr.mp hzero)
  · let : IsLocalRing R := hlocal
    exact Or.inr e.isLocalRing

/-- On a site with a conservative family of points, the local unit-or-unit-complement condition
is equivalent to all stalks of the structure sheaf being zero rings or local rings. -/
@[stacks 04ET "equivalence when the site has enough points", sga "4 IV 13.9" "b) (iii) <=> (iv)"]
theorem locallyUnitOrOneSubUnit_iff_stalksAreZeroOrLocal (X : RingedSite.{u, u, u})
    (hX : X.J.HasConservativeFamily.{u}) :
    LocallyUnitOrOneSubUnit X ↔ StalksAreZeroOrLocal X := by
  constructor
  · exact stalksAreZeroOrLocal_of_locallyUnitOrOneSubUnit X
  · intro hlocal U a
    let S : Sieve U := {
      arrows := fun {V} f =>
        IsUnit (X.O.obj.map f.op a) ∨ IsUnit (1 - X.O.obj.map f.op a)
      downward_closed := by
        intro V W f hfg g
        rcases hfg with hf | hf
        · left
          have hcomp : X.O.obj.map (g ≫ f).op a =
              X.O.obj.map g.op (X.O.obj.map f.op a) := by simp
          rw [hcomp]
          exact hf.map (ConcreteCategory.hom (X.O.obj.map g.op))
        · right
          have hcomp : 1 - X.O.obj.map (g ≫ f).op a =
              X.O.obj.map g.op (1 - X.O.obj.map f.op a) := by simp
          rw [hcomp]
          exact hf.map (ConcreteCategory.hom (X.O.obj.map g.op))
    }
    obtain ⟨P, hP₀⟩ := hX
    have hP := (GrothendieckTopology.isConservativeFamily_subtypeVal_iff P).1 hP₀
    let ι := Σ V : X.C, {f : V ⟶ U // S.arrows f}
    let dom : ι → X.C := fun i => i.1
    let arrows : (i : ι) → dom i ⟶ U := fun i => i.2.1
    have hcoverGen : Sieve.ofArrows dom arrows ∈ X.J U := by
      apply (hP.jointly_reflect_ofArrows_mem (X := U) (U := dom) arrows).2
      intro Φ x
      let R := Φ.obj.presheafFiber.obj X.O.obj
      let : CommRing R := inferInstance
      let T := (Φ.obj.sheafFiber (A := CommRingCat.{u})).obj X.O
      let : CommRing T := inferInstance
      let e : R ≃+* T :=
        (Φ.obj.sheafToPresheafCompPresheafFiberIso.app X.O).commRingCatIsoToRingEquiv
      have hstalk : Subsingleton R ∨ IsLocalRing R := by
        rcases hlocal Φ.obj with hzero | hloc
        · exact Or.inl (e.toEquiv.subsingleton_congr.mpr hzero)
        · let : IsLocalRing T := hloc
          exact Or.inr e.symm.isLocalRing
      let germ := Φ.obj.toPresheafFiber U x X.O.obj a
      have hunit : IsUnit germ ∨ IsUnit (1 - germ) := by
        rcases hstalk with hzero | hloc
        · left
          rw [show germ = 1 from hzero.elim germ 1]
          exact isUnit_one
        · let : IsLocalRing R := hloc
          exact IsLocalRing.isUnit_or_isUnit_one_sub_self germ
      obtain ⟨V, f, y, hxy, hf⟩ :=
        point_exists_unit_or_one_sub_unit_restriction X Φ.obj U x a hunit
      exact ⟨⟨V, ⟨f, hf⟩⟩, y, hxy⟩
    exact ⟨S, X.J.superset_covering (by
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      exact fun i => i.2.2) hcoverGen, fun _ _ hf => hf⟩

/-! ### The equation `1 ≠ 0` -/

attribute [local instance] hasInitialSheafOfTypes

/-- The underlying sheaf of types of the structure sheaf of a ringed site. -/
noncomputable abbrev underlyingStructureSheaf
    (X : RingedSite.{u, v, w}) : Sheaf X.J (Type w) :=
  (sheafForget (D := CommRingCat.{w}) X.J).obj X.O

/-- The global section zero of the underlying structure sheaf. -/
def zeroSection (X : RingedSite.{u, v, w}) :
    Sheaf.terminal X.J Types.isTerminalPUnit.{w} ⟶ underlyingStructureSheaf X :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ (0 : X.O.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change 0 = (X.O.obj.map f).hom 0
       exact (map_zero (X.O.obj.map f).hom).symm }⟩

/-- The global section one of the underlying structure sheaf. -/
def oneSection (X : RingedSite.{u, v, w}) :
    Sheaf.terminal X.J Types.isTerminalPUnit.{w} ⟶ underlyingStructureSheaf X :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ : PUnit.{w + 1} ↦ (1 : X.O.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change 1 = (X.O.obj.map f).hom 1
       exact (map_one (X.O.obj.map f).hom).symm }⟩

/-- The canonical morphism from the empty sheaf to the equalizer of the zero and one sections
of the structure sheaf. -/
@[stacks 05D7]
noncomputable def oneIsNeverZero (X : RingedSite.{u, v, w}) :
    ⊥_ (Sheaf X.J (Type w)) ⟶ equalizer (zeroSection X) (oneSection X) :=
  initial.to _

end AlgebraicGeometry.RingedSite

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

namespace AlgebraicGeometry.RingedSite

/-- Every section of a sheaf of commutative rings is, on some covering, either a unit or has
unit complement. The universe of the rings of sections is independent of the site's. -/
def LocallyEitherUnit {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{w}) : Prop :=
  ∀ (U : C) (f : O.obj.obj (op U)),
    Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering J U
      (fun {_} g ↦ IsUnit (O.obj.map g.op f) ∨ IsUnit (O.obj.map g.op (1 - f)))

/-- When the three universes of a ringed site agree, `LocallyUnitOrOneSubUnit` is equivalent to
`LocallyEitherUnit`. -/
theorem locallyUnitOrOneSubUnit_iff_locallyEitherUnit (X : RingedSite.{u, u, u}) :
    LocallyUnitOrOneSubUnit X ↔ LocallyEitherUnit X.O := by
  refine forall_congr' fun U ↦ forall_congr' fun a ↦ exists_congr fun S ↦ and_congr_right' ?_
  constructor
  · intro h V g hg
    simpa only [map_sub, map_one] using h V g hg
  · intro h V g hg
    simpa only [map_sub, map_one] using h g hg

/-- A ringed site is locally ringed when the sections `0` and `1` of its structure sheaf are
nowhere equal and every section is locally either a unit or has unit complement. -/
@[stacks 04EU]
abbrev IsLocallyRinged (X : RingedSite.{u, v, w}) : Prop :=
  IsIso (oneIsNeverZero X) ∧ LocallyEitherUnit X.O

/-! ### Nonvanishing of the stalks of the structure sheaf -/

/-- For a functor to `Type` which is left exact and preserves colimits, the image of the map
from the initial object to an equalizer is an isomorphism exactly when the two maps being
equalized are nowhere equal. -/
private lemma isIso_map_initialToEqualizer_iff
    {C : Type w} [Category.{w'} C] [HasInitial C] [HasEqualizers C]
    (F : C ⥤ Type u) [PreservesFiniteLimits F] [PreservesColimitsOfSize.{u, u} F]
    {A B : C} (f g : A ⟶ B) :
    IsIso (F.map (initial.to (equalizer f g))) ↔
      ∀ x : F.obj A, F.map f x ≠ F.map g x := by
  let hinit : IsInitial (F.obj (⊥_ C)) := initialIsInitial.isInitialObj F _
  have : IsEmpty (F.obj (⊥_ C)) := (Types.initial_iff_empty _).1 ⟨hinit⟩
  let heq := isLimitOfHasEqualizerOfPreservesLimit F f g
  constructor
  · intro h x hx
    let k : PUnit.{u + 1} ⟶ F.obj A := ↾(fun _ ↦ x)
    have hk : k ≫ F.map f = k ≫ F.map g := by
      ext z
      exact hx
    let y : F.obj (equalizer f g) := (Fork.IsLimit.lift' heq k hk).1 PUnit.unit
    have : IsIso (F.map (initial.to (equalizer f g))) := h
    exact isEmptyElim (inv (F.map (initial.to (equalizer f g))) y)
  · intro h
    rw [isIso_iff_bijective]
    refine ⟨(fun x ↦ isEmptyElim x), ?_⟩
    intro y
    have hy : F.map f (F.map (equalizer.ι f g) y) =
        F.map g (F.map (equalizer.ι f g) y) := by
      rw [← F.map_comp_apply, equalizer.condition, F.map_comp_apply]
    exact (h _ hy).elim

/-- A global section of the structure sheaf with constant value `c` has germ `c`. -/
private lemma sheafFiber_map_section (X : RingedSite.{v, u, u}) (p : X.J.Point.{u})
    (s : Sheaf.terminal X.J Types.isTerminalPUnit.{u} ⟶ underlyingStructureSheaf X)
    (c : ∀ U, X.O.obj.obj U) (hs : ∀ U, s.hom.app U PUnit.unit = c U)
    (r : (p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj)
    (hc : ∀ (U : X.C) (y : p.fiber.obj U), p.toPresheafFiber U y X.O.obj (c (op U)) = r)
    (x : (p.sheafFiber (A := Type u)).obj (Sheaf.terminal X.J Types.isTerminalPUnit.{u})) :
    (p.sheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O
      ((p.sheafFiber (A := Type u)).map s x) = r := by
  change (p.presheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O.obj
    (p.presheafFiber.map s.hom x) = r
  change ToType (p.presheafFiber.obj
    (Sheaf.terminal X.J Types.isTerminalPUnit.{u}).obj) at x
  obtain ⟨U, y, z, rfl⟩ := p.toPresheafFiber_jointly_surjective x
  rw [p.toPresheafFiber_naturality_apply]
  change ((p.toPresheafFiber U y (X.O.obj ⋙ forget CommRingCat.{u}) ≫
    (p.presheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O.obj) (s.hom.app _ z)) = r
  rw [p.toPresheafFiber_presheafFiberCompIso_hom_app]
  exact (congrArg _ (hs _)).trans (hc U y)

/-- The zero section has germ `0`. -/
private lemma sheafFiber_map_zeroSection (X : RingedSite.{v, u, u}) (p : X.J.Point.{u})
    (x : (p.sheafFiber (A := Type u)).obj (Sheaf.terminal X.J Types.isTerminalPUnit.{u})) :
    (p.sheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O
      ((p.sheafFiber (A := Type u)).map (zeroSection X) x) = 0 :=
  sheafFiber_map_section X p _ (fun _ ↦ 0) (fun _ ↦ rfl) 0 (fun _ _ ↦ map_zero _) x

/-- The one section has germ `1`. -/
private lemma sheafFiber_map_oneSection (X : RingedSite.{v, u, u}) (p : X.J.Point.{u})
    (x : (p.sheafFiber (A := Type u)).obj (Sheaf.terminal X.J Types.isTerminalPUnit.{u})) :
    (p.sheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O
      ((p.sheafFiber (A := Type u)).map (oneSection X) x) = 1 :=
  sheafFiber_map_section X p _ (fun _ ↦ 1) (fun _ ↦ rfl) 1 (fun _ _ ↦ map_one _) x

/-- The stalk of `oneIsNeverZero X` at a point `p` is an isomorphism exactly when the stalk of
the structure sheaf at `p` is a nonzero ring. -/
private lemma isIso_sheafFiber_map_oneIsNeverZero_iff (X : RingedSite.{v, u, u})
    (p : X.J.Point.{u}) :
    IsIso ((p.sheafFiber (A := Type u)).map (oneIsNeverZero X)) ↔
      Nontrivial ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) := by
  have : PreservesFiniteLimits (p.sheafFiber (A := Type u)) := inferInstance
  have : PreservesColimitsOfSize.{u, u} (p.sheafFiber (A := Type u)) := inferInstance
  have : HasColimitsOfShape (Discrete PEmpty.{1}) (Sheaf X.J (Type u)) :=
    hasInitialSheafOfTypes X.J
  rw [oneIsNeverZero, isIso_map_initialToEqualizer_iff]
  constructor
  · intro h
    rw [nontrivial_iff]
    refine ⟨0, 1, ?_⟩
    intro h01
    have : IsCofiltered p.fiber.Elements := p.isCofiltered
    let j := Classical.choice (IsCofiltered.nonempty : Nonempty p.fiber.Elements)
    let x : (p.sheafFiber (A := Type u)).obj
        (Sheaf.terminal X.J Types.isTerminalPUnit.{u}) :=
      p.toPresheafFiber j.1 j.2 (Sheaf.terminal X.J Types.isTerminalPUnit.{u}).obj PUnit.unit
    apply h x
    apply ((isIso_iff_bijective
      ((p.sheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O)).mp inferInstance).1
    calc
      _ = 0 := sheafFiber_map_zeroSection X p x
      _ = 1 := h01
      _ = _ := (sheafFiber_map_oneSection X p x).symm
  · intro h x hx
    have hh := congrArg ((p.sheafFiberCompIso (forget CommRingCat.{u})).hom.app X.O) hx
    rw [sheafFiber_map_zeroSection, sheafFiber_map_oneSection] at hh
    exact (zero_ne_one :
      (0 : (p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) ≠ 1) hh

/-- If zero and one are nowhere equal, then the stalk of the structure sheaf at every point is a
nonzero ring. -/
@[stacks 05D8 "the implication (1) ⇒ (2)"]
lemma nontrivial_stalk_of_isIso_oneIsNeverZero (X : RingedSite.{v, u, u})
    [IsIso (oneIsNeverZero X)] (p : X.J.Point.{u}) :
    Nontrivial ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) :=
  (isIso_sheafFiber_map_oneIsNeverZero_iff X p).1 (Functor.map_isIso _ _)

/-- On a site with a conservative family of points, zero and one are nowhere equal if and only if
every stalk of the structure sheaf is a nonzero ring. -/
@[stacks 05D8 "the equivalence (1) ⇔ (2) when the site has enough points"]
lemma isIso_oneIsNeverZero_iff_forall_nontrivial_stalk (X : RingedSite.{v, u, u})
    (hX : X.J.HasConservativeFamily.{u}) :
    IsIso (oneIsNeverZero X) ↔
      ∀ p : X.J.Point.{u}, Nontrivial ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) :=
  ⟨fun _ p ↦ nontrivial_stalk_of_isIso_oneIsNeverZero X p, fun h ↦ by
    obtain ⟨P, hP⟩ := hX
    refine hP _ ?_
    rintro ⟨p, hp⟩
    exact (isIso_sheafFiber_map_oneIsNeverZero_iff X p).2 (h p)⟩

/-! ### The stalk criterion for local ringedness -/

/-- Along a conservative family of points at which the stalk of the structure sheaf is a local
ring, every section of the structure sheaf is, on some covering, either a unit or has unit
complement. -/
@[sga "4 IV 13.9" "b)"]
theorem locallyEitherUnit_of_local_stalks (X : RingedSite.{v, u, u})
    (P : ObjectProperty (X.J.Point.{u})) (hP : P.IsConservativeFamilyOfPoints)
    (hlocal : ∀ p, P p → IsLocalRing ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj)) :
    LocallyEitherUnit X.O := by
  let G : Subfunctor (underlyingStructureSheaf X).obj :=
    { obj := fun U ↦ {a : X.O.obj.obj U | IsUnit a ∨ IsUnit (1 - a)}
      map := by
        intro U V f a ha
        change X.O.obj.obj U at a
        change IsUnit a ∨ IsUnit (1 - a) at ha
        rcases ha with ha | ha
        · exact Or.inl (ha.map (X.O.obj.map f).hom)
        · right
          change IsUnit (1 - (X.O.obj.map f).hom a)
          simpa only [map_sub, map_one] using ha.map (X.O.obj.map f).hom }
  let H : Sheaf X.J (Type u) := ⟨(G.sheafify X.J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (G.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1
        (underlyingStructureSheaf X).property))⟩
  let i : H ⟶ underlyingStructureSheaf X := ⟨(G.sheafify X.J).ι⟩
  have hi : Mono i := (sheafToPresheaf X.J (Type u)).mono_of_mono_map (by
    change Mono (G.sheafify X.J).ι
    infer_instance)
  have hiso : IsIso i := by
    rw [hP.jointlyReflectIsomorphisms_type.isIso_iff]
    intro Φ
    let p := Φ.obj
    let : IsLocalRing ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) :=
      hlocal p Φ.property
    apply (isIso_iff_bijective _).2
    refine ⟨(mono_iff_injective _).1 inferInstance, ?_⟩
    intro a
    obtain ⟨U, x, b, rfl⟩ := p.toPresheafFiber_jointly_surjective
      (P := (underlyingStructureSheaf X).obj) a
    change X.O.obj.obj (op U) at b
    have hunit := IsLocalRing.isUnit_or_isUnit_one_sub_self
      (p.toPresheafFiber U x X.O.obj b)
    have href := point_exists_unit_or_one_sub_unit_restriction X p U x b hunit
    obtain ⟨V, f, y, hy, hu⟩ := href
    let b' : H.obj.obj (op V) := ⟨X.O.obj.map f.op b, G.le_sheafify X.J _ hu⟩
    refine ⟨p.toPresheafFiber V y H.obj b', ?_⟩
    change p.presheafFiber.map i.hom (p.toPresheafFiber V y H.obj b') = _
    rw [p.toPresheafFiber_naturality_apply]
    change p.toPresheafFiber V y (underlyingStructureSheaf X).obj
      ((underlyingStructureSheaf X).obj.map f.op b) = _
    rw [← hy]
    exact p.toPresheafFiber_w_apply f y (underlyingStructureSheaf X).obj b
  let := hiso
  have : IsIso i.hom := (sheafToPresheaf X.J (Type u)).map_isIso i
  intro U a
  have hiapp : Function.Surjective (i.hom.app (op U)) :=
    ((isIso_iff_bijective _).1 (inferInstance : IsIso (i.hom.app (op U)))).2
  obtain ⟨⟨b, hb⟩, hab⟩ := hiapp a
  change b = a at hab
  subst b
  refine ⟨G.sieveOfSection a, hb, ?_⟩
  intro V f hf
  change IsUnit (X.O.obj.map f.op a) ∨ IsUnit (1 - X.O.obj.map f.op a) at hf
  simpa only [map_sub, map_one] using hf

/-- A ringed site is locally ringed as soon as the stalk of its structure sheaf is a local ring at
every point of one conservative family of points of the site. -/
@[sga "4 IV 13.9" "b)"]
theorem isLocallyRinged_of_local_stalks (X : RingedSite.{v, u, u})
    (P : ObjectProperty (X.J.Point.{u})) (hP : P.IsConservativeFamilyOfPoints)
    (hlocal : ∀ p, P p → IsLocalRing ((p.presheafFiber (A := CommRingCat.{u})).obj X.O.obj)) :
    IsLocallyRinged X := by
  refine ⟨?_, locallyEitherUnit_of_local_stalks X P hP hlocal⟩
  rw [hP.jointlyReflectIsomorphisms_type.isIso_iff]
  intro Φ
  let : IsLocalRing ((Φ.obj.presheafFiber (A := CommRingCat.{u})).obj X.O.obj) :=
    hlocal Φ.obj Φ.property
  exact (isIso_sheafFiber_map_oneIsNeverZero_iff X Φ.obj).2 inferInstance

end AlgebraicGeometry.RingedSite
