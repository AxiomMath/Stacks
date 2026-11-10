module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.DGFunctorAdmissible
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated
import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftFunctorStrict

/-!
# A functor of differential graded categories commuting with the shift is exact

Let `F : A ⟶ B` be a functor of differential graded categories over a commutative ring, both
satisfying the direct-sum axiom (A), the shift axiom (B) and the cone axiom (C), and suppose that
`F` commutes with the shift, `F(x[1]) = F(x)[1]`. Then `F` carries an admissible short exact
sequence to an admissible short exact sequence and its connecting morphism to the connecting
morphism of the image, so it carries the triangle of an admissible sequence to the triangle of
the image sequence. Since the distinguished triangles of the homotopy category are exactly those
isomorphic to such a triangle, the induced functor `K(A) ⥤ K(B)` is exact.

## Main definitions

* `DGCategory.ShiftAxiomB.IsStrictKShift`: the property of an axiom (B) datum that the
  translation it puts on the homotopy category is the strict one, that is, that its coherence
  isomorphisms are `eqToIso`s.
* `DGCategory.ShiftAxiomB.strictKShift` and `DGCategory.ShiftAxiomB.strictify`: that strict
  translation, and the axiom (B) datum obtained by substituting it, everything else unchanged;
  `DGCategory.ConeSituation.strictify` is the same for a whole bundle of axioms (A), (B), (C).
* `DGCategory.DGFunctor.CommShiftB`: the hypothesis that `F` commutes with the shift.
* `DGCategory.DGFunctor.CommShiftB.kIso`: the resulting comparison isomorphism
  `shiftFunctor K(A) n ⋙ K(F) ≅ K(F) ⋙ shiftFunctor K(B) n`.
* `DGCategory.DGFunctor.CommShiftB.mapTriangleK`: the induced functor on triangles.
* `DGCategory.DGFunctor.CommShiftK`: the same hypothesis together with the coherence of the
  comparison isomorphisms with the `ℤ`-action data of the translation functors.

## Main results

* `DGCategory.DGFunctor.CommShiftB.mapTriangleK_obj_associatedKTriangle`: the image of the
  triangle of an admissible short exact sequence is the triangle of the image sequence.
* `DGCategory.DGFunctor.CommShiftB.isDistinguishedTriangle_mapTriangleK`: the induced functor
  carries distinguished triangles to distinguished triangles.
* `DGCategory.ShiftAxiomB.onK_shiftFunctor_zero` and
  `DGCategory.ShiftAxiomB.onK_shiftFunctor_add`: the functors induced on the homotopy category by
  the differential graded shifts of axiom (B) satisfy `(-)[0] = 𝟭` and
  `(-)[a + b] = (-)[a] ⋙ (-)[b]` on the nose.
* `DGCategory.ShiftAxiomB.isStrictKShift_strictify`: every axiom (B) datum admits a
  strictification, with the same differential graded shifts.
* `DGCategory.DGFunctor.CommShiftB.kIso_zero_of_isStrictKShift` and
  `DGCategory.DGFunctor.CommShiftB.kIso_add_of_isStrictKShift`: for strict translations the two
  coherences Mathlib's `Functor.CommShift` demands follow from `F(x[1]) = F(x)[1]`, so
  `DGCategory.DGFunctor.CommShiftK.ofCommShiftB` upgrades a `CommShiftB` to a `CommShiftK`.
* `DGCategory.DGFunctor.CommShiftK.commShift` and
  `DGCategory.DGFunctor.CommShiftK.isTriangulated`: the induced functor is an exact functor of
  triangulated categories, in the form of Mathlib's `Functor.CommShift` and
  `Functor.IsTriangulated`.
* `DGCategory.DGFunctor.CommShiftB.isTriangulated` and
  `DGCategory.DGFunctor.CommShiftB.isTriangulated_strictify`: the same conclusion from the
  source's hypothesis `F(x[1]) = F(x)[1]` alone, for strict translations and for the
  strictifications of arbitrary ones.

## Implementation notes

The image of an admissible short exact sequence is
`DGCategory.DGFunctor.mapGradedSplitShortExact` and the identification of the connecting
morphisms is `DGCategory.DGFunctor.connectingHom_mapGradedSplitShortExact`; neither is repeated
here. The triangulated structure on the homotopy categories is the one characterized by Tags
09QW and 09QY, reinstalled with `letI` exactly as in
`StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated`, because the three
axioms are a hypothesis bundle rather than a typeclass.

The hypothesis of the source, `F(x[1]) = F(x)[1]`, is recorded as `CommShiftB`: besides the
equality of objects it asks that `F` commute with the shift functors on homogeneous morphisms and
with the identifications `Hom(x, y)[n] ≅ Hom(x, y[n])` of axiom (B). These are what the proof
uses: the first to make the comparison natural, the second to identify `F(π d(s))` with the
connecting morphism of the image sequence after passing to the shifted object.

Exactness is stated several times over, the statements differing only in how the coherence data
Mathlib's `Functor.CommShift` demands is come by.
`isDistinguishedTriangle_mapTriangleK` is unconditional and is exactness in the encoding of
Tag 09QW, where the distinguished triangles are described by
`DGCategory.IsDistinguishedTriangle`. Mathlib's `Functor.CommShift` additionally demands that the
comparison isomorphisms agree with `shiftFunctorZero` and `shiftFunctorAdd` of the translation
functors, and that agreement is not a consequence of `F(x[1]) = F(x)[1]`: the translation of
`K(A)` is the field `kShift` of `DGCategory.ShiftAxiomB`, which `kShift_functor` constrains to
have the functors induced by the differential graded shifts and constrains in no other way, so
its two coherence isomorphisms are free, and two translations with the same functors may differ
in them.

What the agreement does follow from is the *strictness* of those two isomorphisms,
`DGCategory.ShiftAxiomB.IsStrictKShift` — a property of the ambient axiom (B) data and not a
further hypothesis on `F`. Given it, every isomorphism in sight is an `eqToHom` (`kIso_hom_app`)
and both coherences hold by proof irrelevance, which is
`DGCategory.DGFunctor.CommShiftK.ofCommShiftB`.

That property restricts nothing. `DGCategory.ShiftAxiomB.strictify` replaces the free `kShift`
field by the translation built from the equalities `(-)[0] = 𝟭` and
`(-)[a + b] = (-)[a] ⋙ (-)[b]`, which hold on the nose for the functors induced on `K(A)` by the
differential graded shifts because `zero_obj`, `add_obj`, `zero_map` and `add_map` are equalities
and heterogeneous equalities rather than isomorphisms; every other field of axiom (B) — the
differential graded shift functors themselves, the translation of `A.Comp`, the identifications
`Hom(x, y)[n] ≅ Hom(x, y[n])` — is kept. So `CommShiftB.isTriangulated_strictify` is Tag 0FQF
with no hypothesis beyond the source's, `CommShiftB.isTriangulated` is the same statement for
translations whose strictness the caller already knows, and `CommShiftK` is kept as the form that
takes the two coherences as data, for a translation that is not strict.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory
open CategoryTheory.Limits
open GradedSplitShortExact (associatedKTriangle connectingCocycle connectingHom)

universe u v u' v' w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R} {B : DGCategory.{v', u'} R}

/-- Two cocycles that agree heterogeneously along equalities of their source and target objects
have the same homotopy class, after conjugating by the corresponding `eqToHom`s. -/
private theorem mk_comp_eqToHom_eq {x y x' y' : B.K}
    (f : B.Cocycle (x : B.Obj) (y : B.Obj)) (g : B.Cocycle (x' : B.Obj) (y' : B.Obj))
    (hx : x = x') (hy : y = y') (h : HEq f.1 g.1) :
    (Quotient.mk (B.homotopySetoid (x : B.Obj) (y : B.Obj)) f : x ⟶ y) ≫ eqToHom hy =
      eqToHom hx ≫
        (Quotient.mk (B.homotopySetoid (x' : B.Obj) (y' : B.Obj)) g : x' ⟶ y') := by
  subst hx
  subst hy
  have hfg : f = g := Subtype.ext (eq_of_heq h)
  subst hfg
  simp

/-- Two cocycles that agree heterogeneously along an equality of their targets have the same
homotopy class after correcting their targets by `eqToHom`s. -/
private theorem mk_comp_eqToHom_eq₂ {x y₁ y₂ y₃ : B.K}
    (f : B.Cocycle (x : B.Obj) (y₁ : B.Obj)) (g : B.Cocycle (x : B.Obj) (y₂ : B.Obj))
    (h₁ : y₁ = y₃) (h₂ : y₂ = y₃) (hy : y₁ = y₂) (h : HEq f.1 g.1) :
    (Quotient.mk (B.homotopySetoid (x : B.Obj) (y₁ : B.Obj)) f : x ⟶ y₁) ≫ eqToHom h₁ =
      (Quotient.mk (B.homotopySetoid (x : B.Obj) (y₂ : B.Obj)) g : x ⟶ y₂) ≫ eqToHom h₂ := by
  rw [← eqToHom_trans hy h₂, ← Category.assoc,
    mk_comp_eqToHom_eq f g rfl hy h, eqToHom_refl, Category.id_comp]

/-- **The translation of `K(A)` supplied by axiom (B) is strict.** A `DGCategory.ShiftAxiomB`
carries a `HasShift A.K ℤ` as a field `kShift`, constrained only by `kShift_functor`: for each
`n` the functor `(-)[n]` of that translation *is* the functor `(-)[n]` induced on `K(A)` by the
differential graded shift. Its two coherence isomorphisms `shiftFunctorZero` and
`shiftFunctorAdd` are not constrained at all. This is the property that they are the canonical
ones, that is, `eqToIso` of equalities of functors.

The shifts of the source are strict in this sense: the equalities in question are exactly
`(-)[0] = 𝟭` and `(-)[n + m] = (-)[n] ⋙ (-)[m]`, which hold for the differential graded shift
functors of axiom (B) by its fields `zero_obj`, `add_obj`, `zero_map` and `add_map` and therefore
for the functors they induce on `K(A)`. Nothing below needs the equalities themselves, only that
`shiftFunctorZero` and `shiftFunctorAdd` are the corresponding `eqToIso`s, which is why they are
asked for existentially. -/
def ShiftAxiomB.IsStrictKShift {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) : Prop :=
  letI : HasShift A.K ℤ := S.kShift
  (∃ h : CategoryTheory.shiftFunctor A.K (0 : ℤ) = 𝟭 A.K,
      CategoryTheory.shiftFunctorZero A.K ℤ = eqToIso h) ∧
    ∀ a b : ℤ, ∃ h : CategoryTheory.shiftFunctor A.K (a + b) =
        CategoryTheory.shiftFunctor A.K a ⋙ CategoryTheory.shiftFunctor A.K b,
      CategoryTheory.shiftFunctorAdd A.K a b = eqToIso h

/-- **`(-)[0] = 𝟭` on `K(A)`.** The differential graded shift by `0` of axiom (B) is the identity
on objects and heterogeneously the identity on homogeneous morphisms, by the fields `zero_obj`
and `zero_map`, so the functor it induces on the homotopy category is literally the identity
functor. -/
theorem ShiftAxiomB.onK_shiftFunctor_zero {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) :
    (S.shiftFunctor 0).onK = 𝟭 A.K := by
  refine Functor.hext S.zero_obj (fun x y f => ?_)
  refine Quotient.inductionOn f (fun f => ?_)
  exact homotopyClass_heq _ (S.zero_obj _) (S.zero_obj _) (S.zero_map f.1)

/-- **`(-)[a + b] = (-)[a] ⋙ (-)[b]` on `K(A)`.** As for
`DGCategory.ShiftAxiomB.onK_shiftFunctor_zero`, from the fields `add_obj` and `add_map` of
axiom (B); the two factors occur in the opposite order there, which is why `add_comm` appears. -/
theorem ShiftAxiomB.onK_shiftFunctor_add {A : DGCategory.{v, u} R} (S : ShiftAxiomB A)
    (a b : ℤ) :
    (S.shiftFunctor (a + b)).onK = (S.shiftFunctor a).onK ⋙ (S.shiftFunctor b).onK := by
  have ho : ∀ x : A.Obj,
      (S.shiftFunctor (a + b)).obj x = (S.shiftFunctor b).obj ((S.shiftFunctor a).obj x) := by
    intro x
    rw [add_comm a b]
    exact S.add_obj b a x
  refine Functor.hext ho (fun x y f => ?_)
  refine Quotient.inductionOn f (fun f => ?_)
  refine homotopyClass_heq _ (ho _) (ho _) ?_
  change HEq ((S.shiftFunctor (a + b)).map f.1)
    ((S.shiftFunctor b).map ((S.shiftFunctor a).map f.1))
  rw [add_comm a b]
  exact S.add_map b a f.1

/-- **The strict translation of `K(A)` attached to axiom (B).** The functors are the ones induced
by the differential graded shifts, as `kShift_functor` demands of any translation axiom (B) may
carry, and the two coherence isomorphisms are the `eqToIso`s of
`DGCategory.ShiftAxiomB.onK_shiftFunctor_zero` and
`DGCategory.ShiftAxiomB.onK_shiftFunctor_add`. The three conditions of `ShiftMkCore` are
equalities between composites of `eqToHom`s and hold by proof irrelevance. -/
@[instance_reducible]
def ShiftAxiomB.strictKShift {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) : HasShift A.K ℤ :=
  hasShiftMk A.K ℤ
    { F := fun n => (S.shiftFunctor n).onK
      zero := eqToIso S.onK_shiftFunctor_zero
      add := fun n m => eqToIso (S.onK_shiftFunctor_add n m)
      assoc_hom_app := by
        intro m₁ m₂ m₃ X
        simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
      zero_add_hom_app := by
        intro n X
        simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
      add_zero_hom_app := by
        intro n X
        simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans] }

/-- **Axiom (B) can always be taken with a strict translation on the homotopy category.** The
differential graded data of `S` — its shift functors, its translation of `A.Comp` and its
identifications `Hom(x, y)[n] ≅ Hom(x, y[n])` — are kept unchanged; only the `HasShift A.K ℤ`
field, which `kShift_functor` constrains to have the same functors but whose coherence
isomorphisms are otherwise free, is replaced by the strict one. -/
def ShiftAxiomB.strictify {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) : ShiftAxiomB A :=
  { S with
    kShift := S.strictKShift
    kShift_functor := fun _ => rfl }

/-- Strictifying axiom (B) does not change its differential graded shift functors. -/
@[simp]
theorem ShiftAxiomB.shiftFunctor_strictify {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) :
    S.strictify.shiftFunctor = S.shiftFunctor :=
  rfl

/-- **The strictified axiom (B) datum has a strict translation on the homotopy category.** So the
hypothesis `DGCategory.ShiftAxiomB.IsStrictKShift` restricts nothing about the differential
graded category or its shifts: it only pins down the coherence isomorphisms that the encoding of
axiom (B) leaves free, and every axiom (B) datum admits a strictification with the same
differential graded shifts. -/
theorem ShiftAxiomB.isStrictKShift_strictify {A : DGCategory.{v, u} R} (S : ShiftAxiomB A) :
    S.strictify.IsStrictKShift :=
  ⟨⟨S.onK_shiftFunctor_zero, rfl⟩, fun a b => ⟨S.onK_shiftFunctor_add a b, rfl⟩⟩

/-- The hypothesis `F(x[1]) = F(x)[1]` of Tag 0FQF, in the form in which the proof uses it: the
functor `F` commutes with the shift functors of axiom (B), with their action on homogeneous
morphisms, and with the identifications `Hom(x, y)[n] ≅ Hom(x, y[n])` that axiom (B) provides. -/
structure DGFunctor.CommShiftB (F : DGFunctor A B) (SA : ShiftAxiomB A) (SB : ShiftAxiomB B) where
  /-- `F(x[n]) = F(x)[n]` on objects. -/
  obj : ∀ (n : ℤ) (x : A.Obj),
    F.obj ((SA.shiftFunctor n).obj x) = (SB.shiftFunctor n).obj (F.obj x)
  /-- `F(f[n]) = F(f)[n]` on homogeneous morphisms. -/
  map : ∀ (n : ℤ) {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    HEq (F.map ((SA.shiftFunctor n).map f)) ((SB.shiftFunctor n).map (F.map f))
  /-- `F` commutes with the identification of a degree `k + n` morphism `x ⟶ y` with a degree
  `k` morphism `x ⟶ y[n]`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)),
    HEq (F.map (SA.toShift n x y k f)) (SB.toShift n (F.obj x) (F.obj y) k (F.map f))

namespace DGFunctor.CommShiftB

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- `F(x[n]) = F(x)[n]`, as an equality of objects of `K(B)`. -/
theorem objEqOnK (hF : F.CommShiftB SA SB) (n : ℤ) (x : A.K) :
    ((SA.shiftFunctor n).onK ⋙ F.onK).obj x = (F.onK ⋙ (SB.shiftFunctor n).onK).obj x :=
  hF.obj n (x : A.Obj)

/-- The commutation of `F` with the shift functors of axiom (B), as an isomorphism of functors
on homotopy categories. -/
def onKIso (hF : F.CommShiftB SA SB) (n : ℤ) :
    (SA.shiftFunctor n).onK ⋙ F.onK ≅ F.onK ⋙ (SB.shiftFunctor n).onK :=
  NatIso.ofComponents (fun x => eqToIso (hF.objEqOnK n x)) (by
    intro x y f
    induction f using Quotient.inductionOn with
    | _ f =>
      exact mk_comp_eqToHom_eq (F.mapCocycle ((SA.shiftFunctor n).mapCocycle f))
        ((SB.shiftFunctor n).mapCocycle (F.mapCocycle f))
        (hF.objEqOnK n x) (hF.objEqOnK n y) (hF.map n f.1))

/-- The same commutation isomorphism, written for the translation functors of `K(A)` and
`K(B)` supplied by axiom (B). -/
def kIso (hF : F.CommShiftB SA SB) (n : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    shiftFunctor A.K n ⋙ F.onK ≅ F.onK ⋙ shiftFunctor B.K n :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  Functor.isoWhiskerRight (eqToIso (SA.kShift_functor n)) F.onK ≪≫ hF.onKIso n ≪≫
    Functor.isoWhiskerLeft F.onK (eqToIso (SB.kShift_functor n)).symm

/-- `F(x[n]) = F(x)[n]` for the translation functors of `K(A)` and `K(B)`. -/
theorem objEqK (hF : F.CommShiftB SA SB) (n : ℤ) (x : A.K) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    F.onK.obj ((shiftFunctor A.K n).obj x) = (shiftFunctor B.K n).obj (F.onK.obj x) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  exact (congrArg F.obj (Functor.congr_obj (SA.kShift_functor n) x)).trans
    ((hF.obj n (x : A.Obj)).trans
      (Functor.congr_obj (SB.kShift_functor n) (F.onK.obj x)).symm)

/-- The component at `x` of the forward map of `kIso` is the `eqToHom` of `objEqK`. -/
@[simp]
theorem kIso_hom_app (hF : F.CommShiftB SA SB) (n : ℤ) (x : A.K) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    (hF.kIso n).hom.app x = eqToHom (hF.objEqK n x) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  simp only [kIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToHom_app, eqToIso.hom, eqToIso.inv, onKIso,
    NatIso.ofComponents_hom_app, eqToHom_map]
  simp

/-- **The comparison isomorphism in degree `0` is the canonical one, for strict translations.**
Both sides are families of `eqToHom`s: the left one by `kIso_hom_app`, the right one because
`Functor.CommShift.isoZero` is built out of `shiftFunctorZero` of `K(A)` and of `K(B)`, which
strictness makes `eqToIso`s. Two `eqToHom`s between the same objects are equal. -/
theorem kIso_zero_of_isStrictKShift (hF : F.CommShiftB SA SB)
    (hA : SA.IsStrictKShift) (hB : SB.IsStrictKShift) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    hF.kIso 0 = Functor.CommShift.isoZero F.onK ℤ := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  obtain ⟨hA0, hAeq⟩ := hA.1
  obtain ⟨hB0, hBeq⟩ := hB.1
  ext x
  rw [hF.kIso_hom_app, Functor.CommShift.isoZero_hom_app, hAeq, hBeq]
  simp [eqToHom_map]

/-- **The comparison isomorphisms are additive in the degree, for strict translations.** As for
`kIso_zero_of_isStrictKShift`, both sides are `eqToHom`s between the same objects:
`Functor.CommShift.isoAdd` is built out of `shiftFunctorAdd` of `K(A)` and of `K(B)`, which
strictness makes `eqToIso`s, and out of the comparison isomorphisms in degrees `a` and `b`, which
are `eqToHom`s by `kIso_hom_app`. -/
theorem kIso_add_of_isStrictKShift (hF : F.CommShiftB SA SB)
    (hA : SA.IsStrictKShift) (hB : SB.IsStrictKShift) (a b : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    hF.kIso (a + b) = Functor.CommShift.isoAdd (hF.kIso a) (hF.kIso b) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  obtain ⟨hAab, hAeq⟩ := hA.2 a b
  obtain ⟨hBab, hBeq⟩ := hB.2 a b
  ext x
  rw [hF.kIso_hom_app, Functor.CommShift.isoAdd_hom_app, hAeq, hBeq]
  simp [eqToHom_map]

/-- The functor on triangles induced by `F` and its commutation with the shift: the Mathlib
construction `Functor.mapTriangle` for the comparison isomorphism `kIso`. -/
def mapTriangleK (hF : F.CommShiftB SA SB) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    Pretriangulated.Triangle A.K ⥤ Pretriangulated.Triangle B.K :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  { obj := fun T => Pretriangulated.Triangle.mk (F.onK.map T.mor₁) (F.onK.map T.mor₂)
      (F.onK.map T.mor₃ ≫ (hF.kIso 1).hom.app T.obj₁)
    map := fun {T T'} φ =>
      { hom₁ := F.onK.map φ.hom₁
        hom₂ := F.onK.map φ.hom₂
        hom₃ := F.onK.map φ.hom₃
        comm₁ := by dsimp; simp only [← Functor.map_comp, φ.comm₁]
        comm₂ := by dsimp; simp only [← Functor.map_comp, φ.comm₂]
        comm₃ := by
          dsimp
          simp only [Category.assoc]
          rw [← Functor.map_comp_assoc, ← φ.comm₃, Functor.map_comp, Category.assoc]
          exact congrArg (fun m => F.onK.map T.mor₃ ≫ m)
            ((hF.kIso 1).hom.naturality φ.hom₁).symm }
    map_id := fun T => Pretriangulated.Triangle.hom_ext _ _
      (F.onK.map_id T.obj₁) (F.onK.map_id T.obj₂) (F.onK.map_id T.obj₃)
    map_comp := fun φ ψ => Pretriangulated.Triangle.hom_ext _ _
      (F.onK.map_comp φ.hom₁ ψ.hom₁) (F.onK.map_comp φ.hom₂ ψ.hom₂)
      (F.onK.map_comp φ.hom₃ ψ.hom₃) }

/-- The computation behind `mapTriangleK_obj_associatedKTriangle`, stated for objects of the
homotopy categories: the image of a connecting arrow, followed by the comparison isomorphism,
is the connecting arrow of the image. -/
private theorem map_connecting_comp_kIso (hF : F.CommShiftB SA SB) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    ∀ (x₀ : A.K) {zz u : A.K} {w : B.K}
      (δA : A.Cocycle (zz : A.Obj) (u : A.Obj))
      (δB : B.Cocycle (F.onK.obj zz : B.Obj) (w : B.Obj))
      (p : u = (shiftFunctor A.K 1).obj x₀)
      (q : w = (shiftFunctor B.K 1).obj (F.onK.obj x₀))
      (_ : F.onK.obj u = w)
      (_ : HEq (F.map δA.1) δB.1),
      F.onK.map
            ((Quotient.mk (A.homotopySetoid (zz : A.Obj) (u : A.Obj)) δA : zz ⟶ u) ≫ eqToHom p) ≫
          (hF.kIso 1).hom.app x₀ =
        (Quotient.mk (B.homotopySetoid (F.onK.obj zz : B.Obj) (w : B.Obj)) δB :
            F.onK.obj zz ⟶ w) ≫ eqToHom q := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  intro x₀ zz u w δA δB p q hu hδ
  have happ : (hF.kIso 1).hom.app x₀ = eqToHom (hF.objEqK 1 x₀) := hF.kIso_hom_app 1 x₀
  rw [Functor.map_comp, eqToHom_map, happ, Category.assoc, eqToHom_trans]
  exact mk_comp_eqToHom_eq₂ (F.mapCocycle δA) δB _ q hu hδ

/-- The image of the triangle of an admissible short exact sequence is the triangle of the
image sequence. -/
theorem mapTriangleK_obj_associatedKTriangle (hF : F.CommShiftB SA SB) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    hF.mapTriangleK.obj (associatedKTriangle SA E) =
      associatedKTriangle SB (F.mapGradedSplitShortExact E) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  have hδ : HEq (F.mapCocycle (connectingCocycle SA E)).1
      (connectingCocycle SB (F.mapGradedSplitShortExact E)).1 := by
    have h := hF.toShift 1 z x 0 (connectingHom E)
    rw [← F.connectingHom_mapGradedSplitShortExact E] at h
    exact h
  dsimp only [mapTriangleK, GradedSplitShortExact.associatedKTriangle]
  congr 1
  exact hF.map_connecting_comp_kIso x (connectingCocycle SA E)
    (connectingCocycle SB (F.mapGradedSplitShortExact E)) _ _ (hF.objEqOnK 1 x) hδ

/-- **Tag 0FQF.** The functor induced by `F` on homotopy categories carries the distinguished
triangles of `K(A)` to the distinguished triangles of `K(B)`, the third arrow of the image
triangle being formed with the comparison isomorphism `F(x[1]) = F(x)[1]`. -/
@[stacks 0FQF "distinguished triangles are carried to distinguished triangles"]
theorem isDistinguishedTriangle_mapTriangleK (CA : ConeSituation A) (CB : ConeSituation B)
    (hF : F.CommShiftB CA.shift CB.shift) :
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : HasShift B.K ℤ := CB.shift.kShift
    ∀ T : Pretriangulated.Triangle A.K, IsDistinguishedTriangle A CA T →
      IsDistinguishedTriangle B CB (hF.mapTriangleK.obj T) := by
  let : HasShift A.K ℤ := CA.shift.kShift
  let : HasShift B.K ℤ := CB.shift.kShift
  intro T hT
  obtain ⟨x, y, z, E, ⟨φ⟩⟩ := hT
  exact ⟨F.obj x, F.obj y, F.obj z, F.mapGradedSplitShortExact E,
    ⟨(hF.mapTriangleK.mapIso φ).trans
      (eqToIso (hF.mapTriangleK_obj_associatedKTriangle E))⟩⟩

/-- Any `Functor.CommShift ℤ` structure on the induced functor whose degree-one isomorphism is
the comparison isomorphism `kIso` makes that functor triangulated. -/
theorem onK_isTriangulated (CA : ConeSituation A) (CB : ConeSituation B)
    (hF : F.CommShiftB CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A CA n
    letI : Pretriangulated A.K := homotopyPretriangulated A CA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObject B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditive B CB n
    letI : Pretriangulated B.K := homotopyPretriangulated B CB
    ∀ hcs : F.onK.CommShift ℤ,
      letI := hcs
      F.onK.commShiftIso (1 : ℤ) = hF.kIso 1 → F.onK.IsTriangulated := by
  let : Preadditive A.K := homotopyPreadditive A
  let : HasZeroObject A.K := homotopyHasZeroObject A CA
  let : HasShift A.K ℤ := CA.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A CA n
  let : Pretriangulated A.K := homotopyPretriangulated A CA
  let : Preadditive B.K := homotopyPreadditive B
  let : HasZeroObject B.K := homotopyHasZeroObject B CB
  let : HasShift B.K ℤ := CB.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditive B CB n
  let : Pretriangulated B.K := homotopyPretriangulated B CB
  intro hcs h1
  let := hcs
  have hdistA : Pretriangulated.distinguishedTriangles (C := A.K) =
      {U | IsDistinguishedTriangle A CA U} :=
    distinguishedTriangles_homotopyPretriangulated A CA
  have hdistB : Pretriangulated.distinguishedTriangles (C := B.K) =
      {U | IsDistinguishedTriangle B CB U} :=
    distinguishedTriangles_homotopyPretriangulated B CB
  refine ⟨fun T hT => ?_⟩
  rw [hdistA] at hT
  rw [hdistB]
  have heq : F.onK.mapTriangle.obj T = hF.mapTriangleK.obj T := by
    dsimp only [mapTriangleK]
    rw [← h1]
    rfl
  rw [heq]
  exact hF.isDistinguishedTriangle_mapTriangleK CA CB T hT

end DGFunctor.CommShiftB

/-- The commutation of `F` with the shift together with the coherence of the resulting family of
comparison isomorphisms with the `ℤ`-action data of the translation functors on the homotopy
categories. -/
structure DGFunctor.CommShiftK (F : DGFunctor A B) (SA : ShiftAxiomB A) (SB : ShiftAxiomB B)
    extends DGFunctor.CommShiftB F SA SB where
  /-- The comparison isomorphism in degree `0` is the canonical one. -/
  kIso_zero :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    toCommShiftB.kIso 0 = Functor.CommShift.isoZero F.onK ℤ
  /-- The comparison isomorphisms are additive in the degree. -/
  kIso_add : ∀ a b : ℤ,
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    toCommShiftB.kIso (a + b) =
      Functor.CommShift.isoAdd (toCommShiftB.kIso a) (toCommShiftB.kIso b)

namespace DGFunctor.CommShiftK

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- **The two coherences come for free when the translations of the homotopy categories are
strict.** The hypothesis of Tag 0FQF on `F` is `F(x[1]) = F(x)[1]`, that is, `CommShiftB`; the
two extra fields of `CommShiftK` are not about `F` at all but about the translations of `K(A)` and
`K(B)`, and they hold as soon as those translations are the strict ones of the source, in the
sense of `DGCategory.ShiftAxiomB.IsStrictKShift`. -/
theorem ofCommShiftB (hF : F.CommShiftB SA SB) (hA : SA.IsStrictKShift)
    (hB : SB.IsStrictKShift) :
    F.CommShiftK SA SB where
  toCommShiftB := hF
  kIso_zero := CommShiftB.kIso_zero_of_isStrictKShift hF hA hB
  kIso_add a b := CommShiftB.kIso_add_of_isStrictKShift hF hA hB a b

/-- **Tag 0FQF.** The induced functor `K(A) ⥤ K(B)` commutes with the translation functors. -/
@[instance_reducible, stacks 0FQF "the induced functor commutes with the translations"]
def commShift (hF : F.CommShiftK SA SB) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    F.onK.CommShift ℤ :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  { commShiftIso := hF.toCommShiftB.kIso
    commShiftIso_zero := hF.kIso_zero
    commShiftIso_add := hF.kIso_add }

/-- **Tag 0FQF.** A functor `F : A ⥤ B` of differential graded categories over `R` between
categories satisfying axioms (A), (B) and (C), which commutes with the shift, induces an exact
functor `K(A) ⥤ K(B)` of triangulated categories.

The commutation is asked for here as a `CommShiftK`, that is, together with the two coherences of
the comparison isomorphisms with the `ℤ`-action data of the translations. Under the source's
hypothesis `F(x[1]) = F(x)[1]` alone those two are
`DGCategory.DGFunctor.CommShiftK.ofCommShiftB` away, as soon as the translations of the homotopy
categories are strict; `DGCategory.DGFunctor.CommShiftB.isTriangulated` is that form. -/
@[stacks 0FQF "the induced functor on homotopy categories is exact, from the translation \
  coherences as data", sga "4 Vbis 2.5.1" "more general"]
theorem isTriangulated (CA : ConeSituation A) (CB : ConeSituation B)
    (hF : F.CommShiftK CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A CA n
    letI : Pretriangulated A.K := homotopyPretriangulated A CA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObject B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditive B CB n
    letI : Pretriangulated B.K := homotopyPretriangulated B CB
    letI : F.onK.CommShift ℤ := hF.commShift
    F.onK.IsTriangulated :=
  hF.toCommShiftB.onK_isTriangulated CA CB hF.commShift rfl

end DGFunctor.CommShiftK

namespace DGFunctor.CommShiftB

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- **Tag 0FQF.** A functor `F : A ⥤ B` of differential graded categories over `R` between
categories satisfying axioms (A), (B) and (C) and such that `F(x[1]) = F(x)[1]` induces an exact
functor `K(A) ⥤ K(B)` of triangulated categories.

The hypothesis on `F` is exactly the source's, namely `CommShiftB`; what is assumed besides is
not about `F` but about the two axiom (B) data, namely that the translations they put on the
homotopy categories are the strict ones of the source
(`DGCategory.ShiftAxiomB.IsStrictKShift`). That is what makes the two coherences of
`DGCategory.DGFunctor.CommShiftK` — the agreement of the comparison isomorphisms with
`shiftFunctorZero` and `shiftFunctorAdd`, which Mathlib's `Functor.CommShift` demands and which
`F(x[1]) = F(x)[1]` does not imply for an arbitrary translation — available, by
`DGCategory.DGFunctor.CommShiftK.ofCommShiftB`. -/
@[stacks 0FQF "the induced functor on homotopy categories is exact, from F(x[1]) = F(x)[1]",
  sga "4 Vbis 2.5.1" "more general"]
theorem isTriangulated (CA : ConeSituation A) (CB : ConeSituation B)
    (hA : CA.shift.IsStrictKShift) (hB : CB.shift.IsStrictKShift)
    (hF : F.CommShiftB CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A CA n
    letI : Pretriangulated A.K := homotopyPretriangulated A CA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObject B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditive B CB n
    letI : Pretriangulated B.K := homotopyPretriangulated B CB
    letI : F.onK.CommShift ℤ := (CommShiftK.ofCommShiftB hF hA hB).commShift
    F.onK.IsTriangulated :=
  (CommShiftK.ofCommShiftB hF hA hB).isTriangulated CA CB

end DGFunctor.CommShiftB

/-- **Axioms (A), (B) and (C) can always be taken with a strict translation on the homotopy
category**, by `DGCategory.ShiftAxiomB.strictify`: the cone data are untouched, and the shifted
objects and connecting cocycles they refer to are unchanged, the differential graded shift
functors and the identifications `Hom(x, y)[n] ≅ Hom(x, y[n])` being the same. -/
def ConeSituation.strictify (C : ConeSituation A) : ConeSituation A :=
  { C with shift := C.shift.strictify }

/-- The strictified cone situation has a strict translation on the homotopy category. -/
theorem ConeSituation.isStrictKShift_strictify (C : ConeSituation A) :
    C.strictify.shift.IsStrictKShift :=
  C.shift.isStrictKShift_strictify

namespace DGFunctor.CommShiftB

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- The hypothesis `F(x[1]) = F(x)[1]` is about the differential graded shift functors and the
identifications `Hom(x, y)[n] ≅ Hom(x, y[n])` only, so it holds for the strictifications of the
two axiom (B) data as soon as it holds for them. -/
theorem strictify (hF : F.CommShiftB SA SB) : F.CommShiftB SA.strictify SB.strictify where
  obj := hF.obj
  map := hF.map
  toShift := hF.toShift

/-- **Tag 0FQF, with nothing assumed but the source's hypothesis.** A functor `F : A ⥤ B` of
differential graded categories over `R` between categories satisfying axioms (A), (B) and (C) and
such that `F(x[1]) = F(x)[1]` induces an exact functor `K(A) ⥤ K(B)` of triangulated categories,
for the triangulated structures attached to the strictifications of the two axiom bundles.

Passing to the strictifications changes nothing about the differential graded categories, their
shifts, their cones or the distinguished triangles of Tag 09QW: it only replaces the `HasShift`
field of axiom (B), whose functors `kShift_functor` already pins down, by the one whose coherence
isomorphisms are the canonical ones. So this is Tag 0FQF with no hypothesis beyond the source's
`F(x[1]) = F(x)[1]`, and `DGCategory.DGFunctor.CommShiftB.isTriangulated` is the form in which
the strictness is left as a hypothesis, for a caller who already knows it of the translations
in hand. -/
@[stacks 0FQF "the induced functor on homotopy categories is exact, from F(x[1]) = F(x)[1] alone",
  sga "4 Vbis 2.5.1" "more general"]
theorem isTriangulated_strictify (CA : ConeSituation A) (CB : ConeSituation B)
    (hF : F.CommShiftB CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObject A CA.strictify
    letI : HasShift A.K ℤ := CA.strictify.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n =>
      homotopyShiftAdditive A CA.strictify n
    letI : Pretriangulated A.K := homotopyPretriangulated A CA.strictify
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObject B CB.strictify
    letI : HasShift B.K ℤ := CB.strictify.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n =>
      homotopyShiftAdditive B CB.strictify n
    letI : Pretriangulated B.K := homotopyPretriangulated B CB.strictify
    letI : F.onK.CommShift ℤ := (CommShiftK.ofCommShiftB hF.strictify
      CA.isStrictKShift_strictify CB.isStrictKShift_strictify).commShift
    F.onK.IsTriangulated :=
  isTriangulated CA.strictify CB.strictify CA.isStrictKShift_strictify
    CB.isStrictKShift_strictify hF.strictify

end DGFunctor.CommShiftB

end DGCategory
