module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.Finite.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits

/-!
# A smallness hypothesis on the index is necessary for inverse limits of schemes

Mathlib's `Mathlib.AlgebraicGeometry.AffineTransitionLimit` develops inverse limits of schemes
with affine transition morphisms for an index category `I : Type u` with `[Category.{u} I]`,
i.e. at the *same* universe as the schemes `Scheme.{u}`.
`StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit` frees the index universe
at the cost of `CategoryTheory.LocallySmall.{u} I` and `CategoryTheory.InitiallySmall.{u} I`.
This file shows that the second of those hypotheses cannot be dropped, by exhibiting a directed
inverse system of **nonempty affine** schemes with **affine** transition morphisms, indexed by a
directed preorder one universe up, whose limit in `Scheme.{u}` is the **empty** scheme.

The index is `Ordinal.{u}`, a directed preorder in `Type (u + 1)` no `u`-small subset of which is
cofinal. The stage `o` is the spectrum of `Fld o`, the rational function field over `𝔽₂` on `o`
many variables, the variables of stage `o` being the elements of `o.ToType`; the transition
morphism for `o ≤ p` is induced by the canonical initial-segment embedding of variables. The
filtered colimit of this chain is a field that is not `u`-small, so it admits no homomorphism to
a nonzero ring in `Type u`. Hence no scheme with a point carries a cone over the system, and the
empty scheme is a genuine limit cone.

Consequently the whole family of `Mathlib.AlgebraicGeometry.AffineTransitionLimit` results is
false when the index universe is allowed to exceed the scheme universe with no condition on the
index: `AlgebraicGeometry.Scheme.nonempty_of_isLimit` (Stacks Tag 01Z2) already fails. The
system is packaged as an `AlgebraicGeometry.DescentSituation`, so it is a legal instantiation of
every statement made in that standing situation, among them Stacks Tag 01Z0.

## Main definitions

* `Stacks.AlgebraicGeometry.SmallnessNecessary.Fld` is the chain of rational function fields, and
  `fldMap` its transition homomorphisms; `fldFunctor` packages them as a functor out of
  `Ordinal.{u}`.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.system` is the resulting inverse system of
  spectra, and `emptyCone` the cone over it whose apex is the empty scheme.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.Compatible` is a compatible family of ring
  homomorphisms out of the chain.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.situation` is the system as a
  `AlgebraicGeometry.DescentSituation.{u + 1, u} Ordinal.{u}`.

## Main results

* `Stacks.AlgebraicGeometry.SmallnessNecessary.subsingleton_of_compatible`: no nonzero ring in
  `Type u` receives the whole chain of fields compatibly.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.isEmpty_cone_pt` and
  `Stacks.AlgebraicGeometry.SmallnessNecessary.emptyConeIsLimit`: every cone over the system has
  empty apex, and the empty cone is a limit cone.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.isEmpty_situation_limit`,
  `Stacks.AlgebraicGeometry.SmallnessNecessary.nonempty_situation_obj` and
  `Stacks.AlgebraicGeometry.SmallnessNecessary.isAffine_situation_obj`: the limit of the
  situation is empty while every stage is a nonempty affine scheme.
* `Stacks.AlgebraicGeometry.SmallnessNecessary.subsingleton_Γ_situation_limit` and
  `Stacks.AlgebraicGeometry.SmallnessNecessary.nontrivial_Γ_situation_obj`: the global sections
  of the limit are the zero ring while the global sections at every stage form a field.

## Implementation notes

Functoriality of the chain is free rather than computed: the transition map on variables is the
canonical initial-segment embedding, and initial-segment embeddings between well-orders are
unique, so `CategoryTheory.Subsingleton` of `InitialSeg` gives both functor laws. The transition
maps on fields are obtained from the maps on polynomial rings by `IsFractionRing.lift`, and their
functor laws follow from `IsLocalization.ringHom_ext`.

That a nonzero receiving ring would be `u`-small-impossible is witnessed concretely: the ordinal
`o` is sent to the image of the last variable of the stage `o + 1`, and distinct ordinals give
distinct elements because the initial-segment embeddings preserve `Ordinal.typein` and a
homomorphism out of a field into a nonzero ring is injective. That produces an injection of
`Ordinal.{u}` into a type in `Type u`, contradicting `not_small_ordinal`.

The same pathology is built a second time in
`StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic`, over the finitely generated
subrings of a non-`u`-small field rather than over `Ordinal.{u}`: its `isEmpty_cone_pt` is stated
for every field that is not `u`-small, so it subsumes the system below, and
`StacksFrontier.AlgebraicGeometry.LimitSectionsCounterexample.Basic` packages that system as a
descent situation exactly as `situation` does. What only this file has is the instantiation of
`AlgebraicGeometry.DescentSituation` itself; the other packaging instantiates a local restatement
of the same structure.

`CategoryTheory.not_initiallySmall_op_ordinal` in
`StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic` records the companion fact that
`CategoryTheory.InitiallySmall.{u} (Ordinal.{u})ᵒᵖ` itself fails; the point of this file is the
stronger one that the *conclusions* of the limit theorems fail, not merely that the route to them
is unavailable.

## References

* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 086P](https://stacks.math.columbia.edu/tag/086P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SmallnessNecessary

/-- The variable set of stage `o`: the underlying type of the ordinal `o`. -/
abbrev Vars (o : Ordinal.{u}) : Type u := o.ToType

/-- The canonical initial-segment embedding of the variables of stage `o` into those of a later
stage `p`. -/
def varMap {o p : Ordinal.{u}} (h : o ≤ p) :
    InitialSeg (α := Vars o) (· < ·) (β := Vars p) (· < ·) :=
  Classical.choice (Ordinal.type_le_iff.mp (by rwa [Ordinal.type_toType, Ordinal.type_toType]))

/-- Two initial-segment embeddings between the variable sets of two stages agree pointwise. -/
private lemma initialSeg_apply_eq {o p : Ordinal.{u}}
    (f g : InitialSeg (α := Vars o) (· < ·) (β := Vars p) (· < ·)) (x : Vars o) : f x = g x := by
  rw [Subsingleton.elim f g]

/-- The embeddings `varMap` compose: `varMap h₂ ∘ varMap h₁ = varMap (h₁.trans h₂)`. -/
lemma varMap_varMap {o p q : Ordinal.{u}} (h₁ : o ≤ p) (h₂ : p ≤ q) (x : Vars o) :
    varMap h₂ (varMap h₁ x) = varMap (h₁.trans h₂) x :=
  initialSeg_apply_eq ((varMap h₁).trans (varMap h₂)) _ x

/-- The embedding `varMap` of a stage into itself is the identity. -/
lemma varMap_self {o : Ordinal.{u}} (x : Vars o) : varMap (le_refl o) x = x :=
  initialSeg_apply_eq (varMap (le_refl o)) (InitialSeg.refl _) x

/-- The embedding `varMap` preserves the position `Ordinal.typein` of each variable. -/
lemma typein_varMap {o p : Ordinal.{u}} (h : o ≤ p) (x : Vars o) :
    Ordinal.typein (α := Vars p) (· < ·) (varMap h x) =
      Ordinal.typein (α := Vars o) (· < ·) x :=
  Ordinal.typein_apply (varMap h) x

/-! ### The chain of fields -/

/-- The polynomial ring over `𝔽₂` on the variables of stage `o`. -/
abbrev Poly (o : Ordinal.{u}) : Type u := MvPolynomial (Vars o) (ZMod 2)

/-- The rational function field over `𝔽₂` on the variables of stage `o`. -/
abbrev Fld (o : Ordinal.{u}) : Type u := FractionRing (Poly o)

/-- The polynomial ring `Poly o` is an integral domain. -/
instance isDomain_poly (o : Ordinal.{u}) : IsDomain (Poly o) :=
  inferInstanceAs (IsDomain (MvPolynomial (Vars o) (ZMod 2)))

/-- `Fld o` is a field. -/
instance field_fld (o : Ordinal.{u}) : Field (Fld o) :=
  inferInstanceAs (Field (FractionRing (Poly o)))

/-- `Fld o` is an algebra over `Poly o`. -/
instance algebra_poly_fld (o : Ordinal.{u}) : Algebra (Poly o) (Fld o) :=
  inferInstanceAs (Algebra (Poly o) (FractionRing (Poly o)))

/-- `Fld o` is the fraction field of `Poly o`. -/
instance isFractionRing_poly_fld (o : Ordinal.{u}) : IsFractionRing (Poly o) (Fld o) :=
  inferInstanceAs (IsFractionRing (Poly o) (FractionRing (Poly o)))

/-- Renaming the variables along `varMap`. -/
def polyMap {o p : Ordinal.{u}} (h : o ≤ p) : Poly o →+* Poly p :=
  (MvPolynomial.rename (varMap h)).toRingHom

/-- `polyMap h` is `MvPolynomial.rename` along `varMap h`. -/
lemma polyMap_apply {o p : Ordinal.{u}} (h : o ≤ p) (x : Poly o) :
    polyMap h x = MvPolynomial.rename (varMap h) x := rfl

/-- `polyMap h` is injective. -/
lemma polyMap_injective {o p : Ordinal.{u}} (h : o ≤ p) :
    Function.Injective (polyMap h) :=
  MvPolynomial.rename_injective _ (varMap h).injective

/-- `polyMap h` sends the variable `x` to the variable `varMap h x`. -/
lemma polyMap_X {o p : Ordinal.{u}} (h : o ≤ p) (x : Vars o) :
    polyMap h (MvPolynomial.X x) = MvPolynomial.X (varMap h x) := by
  simp [polyMap_apply]

/-- The maps `polyMap` compose: `polyMap h₂ ∘ polyMap h₁ = polyMap (h₁.trans h₂)`. -/
lemma polyMap_polyMap {o p q : Ordinal.{u}} (h₁ : o ≤ p) (h₂ : p ≤ q) (x : Poly o) :
    polyMap h₂ (polyMap h₁ x) = polyMap (h₁.trans h₂) x := by
  have hf : ((varMap h₂ : Vars p → Vars q) ∘ (varMap h₁ : Vars o → Vars p)) =
      (varMap (h₁.trans h₂) : Vars o → Vars q) := funext (varMap_varMap h₁ h₂)
  rw [polyMap_apply, polyMap_apply, polyMap_apply, MvPolynomial.rename_rename, hf]

/-- The map `polyMap` of a stage into itself is the identity. -/
lemma polyMap_self {o : Ordinal.{u}} (x : Poly o) : polyMap (le_refl o) x = x := by
  rw [polyMap_apply, show ((varMap (le_refl o) : Vars o → Vars o)) = id from funext varMap_self]
  simp

/-- The induced embedding of rational function fields. -/
def fldMap {o p : Ordinal.{u}} (h : o ≤ p) : Fld o →+* Fld p :=
  IsFractionRing.lift (A := Poly o) (K := Fld o) (L := Fld p)
    (g := (algebraMap (Poly p) (Fld p)).comp (polyMap h))
    (by
      rw [RingHom.coe_comp]
      exact (IsFractionRing.injective (Poly p) (Fld p)).comp (polyMap_injective h))

/-- On polynomials, `fldMap h` is `polyMap h`. -/
@[simp]
lemma fldMap_algebraMap {o p : Ordinal.{u}} (h : o ≤ p) (x : Poly o) :
    fldMap h (algebraMap (Poly o) (Fld o) x) = algebraMap (Poly p) (Fld p) (polyMap h x) :=
  IsFractionRing.lift_algebraMap (A := Poly o) (K := Fld o) (L := Fld p) _ x

/-- Two ring homomorphisms out of `Fld o` agreeing on polynomials are equal. -/
lemma fld_ringHom_ext {o : Ordinal.{u}} {L : Type*} [CommRing L] {f g : Fld o →+* L}
    (h : f.comp (algebraMap (Poly o) (Fld o)) = g.comp (algebraMap (Poly o) (Fld o))) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (Poly o)) h

/-- The map `fldMap` of a stage into itself is the identity. -/
lemma fldMap_self {o : Ordinal.{u}} : fldMap (le_refl o) = RingHom.id _ := by
  refine fld_ringHom_ext (RingHom.ext fun x => ?_)
  simp [polyMap_self]

/-- The maps `fldMap` compose: `fldMap h₂ ∘ fldMap h₁ = fldMap (h₁.trans h₂)`. -/
lemma fldMap_fldMap {o p q : Ordinal.{u}} (h₁ : o ≤ p) (h₂ : p ≤ q) :
    (fldMap h₂).comp (fldMap h₁) = fldMap (h₁.trans h₂) := by
  refine fld_ringHom_ext (RingHom.ext fun x => ?_)
  simp [polyMap_polyMap]

/-! ### The inverse system -/

/-- The chain of fields, as a functor out of the ordinals. -/
def fldFunctor : Ordinal.{u} ⥤ CommRingCat.{u} where
  obj o := CommRingCat.of (Fld o)
  map {_ _} h := CommRingCat.ofHom (fldMap (leOfHom h))
  map_id o := by
    ext x
    simpa using congrArg (fun f : Fld o →+* Fld o => f x) fldMap_self
  map_comp {o p q} f g := by
    ext x
    exact (congrArg (fun f : Fld o →+* Fld q => f x)
      (fldMap_fldMap (leOfHom f) (leOfHom g))).symm

/-- The inverse system of the spectra of the chain of fields, indexed by the ordinals. -/
def system : Ordinal.{u}ᵒᵖ ⥤ Scheme.{u} := fldFunctor.{u}.op ⋙ Scheme.Spec

/-- The stage `o` of `system` is the spectrum of `Fld o`. -/
lemma system_obj (o : Ordinal.{u}) :
    system.{u}.obj (op o) = Spec (CommRingCat.of (Fld o)) := rfl

/-- The transition morphism of `system` for `o ≤ p` is the spectrum of `fldMap`. -/
lemma system_map {o p : Ordinal.{u}} (h : o ≤ p) :
    system.{u}.map (homOfLE h).op = Spec.map (CommRingCat.ofHom (fldMap h)) := rfl

/-- Every stage of `system` is a nonempty scheme. -/
instance nonempty_system_obj (i : Ordinal.{u}ᵒᵖ) : Nonempty (system.{u}.obj i) :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of (Fld i.unop))))

/-- Every transition morphism of `system` is affine. -/
instance isAffineHom_system_map {i j : Ordinal.{u}ᵒᵖ} (g : i ⟶ j) :
    IsAffineHom (system.{u}.map g) :=
  inferInstanceAs (IsAffineHom (Spec.map (fldFunctor.{u}.map g.unop)))

/-- Every stage of `system` is quasi-compact. -/
instance compactSpace_system_obj (i : Ordinal.{u}ᵒᵖ) : CompactSpace (system.{u}.obj i) :=
  inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Fld i.unop))))

/-- Every stage of `system` is quasi-separated. -/
instance quasiSeparatedSpace_system_obj (i : Ordinal.{u}ᵒᵖ) :
    QuasiSeparatedSpace (system.{u}.obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Fld i.unop))))

/-! ### No nonzero `u`-small ring receives the whole chain -/

/-- The last variable of the stage `o + 1`. -/
def topVar (o : Ordinal.{u}) : Vars (o + 1) :=
  Ordinal.enum (α := Vars (o + 1)) (· < ·) ⟨o, by rw [Ordinal.type_toType]; exact lt_add_one o⟩

/-- The variable `topVar o` sits at position `o` in the stage `o + 1`. -/
lemma typein_topVar (o : Ordinal.{u}) :
    Ordinal.typein (α := Vars (o + 1)) (· < ·) (topVar o) = o :=
  Ordinal.typein_enum _ _

/-- A compatible family of ring homomorphisms out of the chain of fields. -/
structure Compatible (Z : Type u) [CommRing Z] where
  /-- The homomorphism at stage `o`. -/
  hom (o : Ordinal.{u}) : Fld o →+* Z
  /-- The homomorphisms are compatible with the transition maps of the chain. -/
  hom_fldMap {o p : Ordinal.{u}} (h : o ≤ p) (x : Fld o) : hom p (fldMap h x) = hom o x

namespace Compatible

variable {Z : Type u} [CommRing Z] [Nontrivial Z] (t : Compatible.{u} Z)

/-- Each homomorphism of a compatible family into a nonzero ring is injective. -/
lemma injective (o : Ordinal.{u}) : Function.Injective (t.hom o) := RingHom.injective _

/-- The element of `Z` attached to the ordinal `o`: the image of the last variable of the stage
`o + 1`. -/
def witness (o : Ordinal.{u}) : Z :=
  t.hom (o + 1) (algebraMap (Poly (o + 1)) (Fld (o + 1)) (MvPolynomial.X (topVar o)))

omit [Nontrivial Z] in
/-- The element `t.witness o` is the image under `t.hom q` of the variable `topVar o`, carried
to any later stage `q` along `varMap`. -/
lemma witness_eq {o q : Ordinal.{u}} (h : o + 1 ≤ q) :
    t.witness o = t.hom q (algebraMap (Poly q) (Fld q) (MvPolynomial.X (varMap h (topVar o)))) := by
  rw [witness, ← t.hom_fldMap h, fldMap_algebraMap, polyMap_X]

/-- Distinct ordinals have distinct witnesses. -/
lemma witness_injective : Function.Injective t.witness := by
  intro o o' hoo'
  have h₁ : o + 1 ≤ max (o + 1) (o' + 1) := le_max_left _ _
  have h₂ : o' + 1 ≤ max (o + 1) (o' + 1) := le_max_right _ _
  rw [t.witness_eq h₁, t.witness_eq h₂] at hoo'
  have hX := MvPolynomial.X_injective (R := ZMod 2)
    ((IsFractionRing.injective (Poly _) (Fld _)) (t.injective _ hoo'))
  have := congrArg (Ordinal.typein (α := Vars _) (· < ·)) hX
  rwa [typein_varMap, typein_varMap, typein_topVar, typein_topVar] at this

end Compatible

/-- **No nonzero ring in the universe of the schemes receives the whole chain of fields
compatibly.** Equivalently: the filtered colimit of the chain is not `u`-small. A nonzero
receiving ring would be a `u`-small type containing an injective image of `Ordinal.{u}`, because
every homomorphism out of a field into a nonzero ring is injective, and distinct ordinals label
distinct variables. -/
theorem subsingleton_of_compatible {Z : Type u} [CommRing Z] (t : Compatible.{u} Z) :
    Subsingleton Z := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hZ
  exact not_small_ordinal.{u, u} (small_of_injective t.witness_injective)

/-! ### Every cone over the system has empty apex -/

/-- The global sections of the stage-`o` scheme are the stage-`o` field. -/
def ΓIso (o : Ordinal.{u}) : Γ(system.{u}.obj (op o), ⊤) ≅ CommRingCat.of (Fld o) :=
  Scheme.ΓSpecIso (CommRingCat.of (Fld o))

/-- The inverses of `ΓIso` are natural with respect to the transition maps. -/
lemma ΓIso_inv_naturality {o p : Ordinal.{u}} (h : o ≤ p) :
    CommRingCat.ofHom (fldMap h) ≫ (ΓIso p).inv =
      (ΓIso o).inv ≫ (system.{u}.map (homOfLE h).op).appTop :=
  Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (fldMap h))

/-- A cone over the system gives a compatible family of ring homomorphisms out of the chain of
fields, landing in the global sections of the apex. -/
def coneCompatible (s : Cone system.{u}) : Compatible.{u} Γ(s.pt, ⊤) where
  hom o := ((ΓIso o).inv ≫ (s.π.app (op o)).appTop).hom
  hom_fldMap {o p} h x := by
    have hmor : CommRingCat.ofHom (fldMap h) ≫ ((ΓIso p).inv ≫ (s.π.app (op p)).appTop) =
        (ΓIso o).inv ≫ (s.π.app (op o)).appTop := by
      rw [← Category.assoc, ΓIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop,
        s.w (homOfLE h).op]
    simpa using (elementwise_of% hmor) x

/-- The whole space of a nonempty scheme is nonempty. -/
lemma nonempty_top_of_nonempty (X : Scheme.{u}) (hX : Nonempty X) : Nonempty (⊤ : X.Opens) :=
  ⟨⟨hX.some, trivial⟩⟩

/-- **Every cone over the system has empty apex.** If the apex were nonempty its ring of global
sections would be a nonzero `u`-small ring receiving the whole chain. -/
lemma isEmpty_cone_pt (s : Cone system.{u}) : IsEmpty s.pt := by
  rw [← not_nonempty_iff]
  intro hs
  have := nonempty_top_of_nonempty s.pt hs
  have : Nontrivial Γ(s.pt, ⊤) := Scheme.component_nontrivial s.pt ⊤
  exact (not_subsingleton _) (subsingleton_of_compatible (coneCompatible s))

/-! ### The limit cone, and the descent situation it realizes -/

/-- The cone over the system whose apex is the empty scheme. -/
def emptyCone : Cone system.{u} where
  pt := ∅
  π := { app := fun _ => Scheme.emptyTo _, naturality := fun _ _ _ => Scheme.empty_ext _ _ }

/-- **The empty cone is a limit cone.** Every cone over the system has empty apex, hence is
initial, hence maps uniquely to the empty scheme. -/
def emptyConeIsLimit : IsLimit emptyCone.{u} where
  lift s := have := isEmpty_cone_pt s; (isInitialOfIsEmpty (X := s.pt)).to _
  fac s _ := have := isEmpty_cone_pt s; (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _
  uniq s _ _ := have := isEmpty_cone_pt s; (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _

/-- The system, together with its empty limit, as an `AlgebraicGeometry.DescentSituation` over
the directed preorder `Ordinal.{u}` — which lives at the universe `u + 1`, independent of the
universe `u` of the schemes. -/
def situation : AlgebraicGeometry.DescentSituation.{u + 1, u} Ordinal.{u} where
  system := system
  transition_affine _ := inferInstance
  quasiCompact _ := inferInstance
  quasiSeparated _ := inferInstance
  limitCone := emptyCone
  isLimit := emptyConeIsLimit
  base := 0

/-- Every stage of the situation is a nonempty scheme. -/
theorem nonempty_situation_obj (i : Ordinal.{u}ᵒᵖ) :
    Nonempty (situation.{u}.system.obj i) :=
  inferInstanceAs (Nonempty (system.{u}.obj i))

/-- Every stage of the situation is an affine, hence quasi-compact and quasi-separated, scheme. -/
theorem isAffine_situation_obj (i : Ordinal.{u}ᵒᵖ) :
    IsAffine (situation.{u}.system.obj i) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (Fld i.unop))))

/-- **The limit of the situation is the empty scheme**, even though every stage is a nonempty
affine scheme and every transition morphism is affine. -/
theorem isEmpty_situation_limit : IsEmpty (situation.{u}.limitCone.pt) :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

/-- The global sections of the limit of the situation are the zero ring. -/
theorem subsingleton_Γ_situation_limit : Subsingleton Γ(situation.{u}.limitCone.pt, ⊤) :=
  inferInstanceAs (Subsingleton Γ((∅ : Scheme.{u}), ⊤))

/-- The global sections at every stage of the situation form a field, in particular a nonzero
ring. -/
theorem nontrivial_Γ_situation_obj (i : Ordinal.{u}ᵒᵖ) :
    Nontrivial Γ(situation.{u}.system.obj i, ⊤) :=
  have := nonempty_top_of_nonempty (system.{u}.obj i) inferInstance
  Scheme.component_nontrivial (system.{u}.obj i) ⊤

end Stacks.AlgebraicGeometry.SmallnessNecessary
