module

public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ring objects transported along a braided functor

Mathlib has ring objects in a cartesian monoidal category (`CategoryTheory.RingObj`) and the
category `CategoryTheory.RingObjCat` they form, but nothing that moves them: there is no
analogue of `CategoryTheory.Functor.mapGrp` for `RingObj`, so a finite-product-preserving
functor does not yet act on internal rings at all. This file supplies that action, in the same
shape as `Mathlib/CategoryTheory/Monoidal/Grp.lean` gives it for group objects.

A ring object is an additive group object whose addition is commutative, together with a
multiplicative monoid structure, subject to the two distributivity identities. A braided functor
between cartesian monoidal categories carries the first three over by Mathlib's
`CategoryTheory.Functor.addGrpObjObj`, `CategoryTheory.Functor.monObjObj` and the additive form
of `CategoryTheory.Functor.isCommMonObj_obj` recorded here; the two distributivity identities are
transported by applying the functor to them and cancelling the comparison isomorphism `δ`, which
is invertible because the functor is strong monoidal.

## Main definitions

* `CategoryTheory.RingObjCat.mkIso` — an isomorphism of ring objects from an isomorphism of the
  underlying objects which respects the four structure morphisms.
* `CategoryTheory.Functor.ringObjObjOfBraided` — the image of a ring object under a braided
  functor is a ring object.
* `CategoryTheory.Functor.mapRing` — the induced functor `RingObjCat C ⥤ RingObjCat D`.
* `CategoryTheory.Functor.mapRingCompIso` and `CategoryTheory.Functor.mapRingNatIso` — the
  composition and naturality comparisons, the ring analogues of
  `CategoryTheory.Functor.mapGrpCompIso` and `CategoryTheory.Functor.mapGrpNatIso`.

## Implementation notes

`mapRing` asks for `CategoryTheory.Functor.Braided` where `mapGrp` asks only for
`CategoryTheory.Functor.Monoidal`: a ring object has a commutativity to transport, namely that of
its addition, and transporting it needs the braiding. For a functor between cartesian monoidal
categories this is no extra hypothesis — `CategoryTheory.Functor.Braided.ofChosenFiniteProducts`
produces it from preservation of finite products — but it does have to be supplied, and the
`Monoidal` instance underlying it must be the same one, which is why call sites fix the braided
structure rather than the monoidal structure.

The two distributivity transports are proved by cancelling `δ` rather than by `simp`: the
simp normal form pushes `X ◁ (f ≫ g)` apart into `X ◁ f ≫ X ◁ g`, which prevents the
cancellation `δ ≫ μ = 𝟙` from firing under a whiskering.

The four structure morphisms of a composite are compared in `comp_mapRing_one` and its siblings,
each stated between two `RingObj` structures which are *not* definitionally equal: the one
obtained in one step along `F ⋙ G` multiplies out `G.map (ε F ≫ F.map η)` where the one
obtained in two steps has `G.map (ε F) ≫ G.map (F.map η)`, and only
`CategoryTheory.Functor.map_comp` identifies them. Each proof therefore opens with a `show` that
spells both sides out: without it
`simp` cannot see past the `RingObj` projection to apply
`CategoryTheory.Functor.obj.η_def` and its siblings.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E] [BraidedCategory E]

open scoped Obj MonObj AddMonObj

namespace RingObjCat

/-- An isomorphism of the underlying objects which is a homomorphism of ring objects is an
isomorphism of ring objects. -/
public def mkIso' {R₁ R₂ : C} [RingObj R₁] [RingObj R₂] (e : R₁ ≅ R₂) [IsRingHom e.hom] :
    RingObjCat.mk R₁ ≅ RingObjCat.mk R₂ where
  hom := Hom.mk e.hom
  inv :=
    haveI : IsRingHom e.inv := ⟨⟩
    Hom.mk e.inv

/-- **An isomorphism of ring objects from an isomorphism of the underlying objects.** Only the
forward direction of the four compatibilities has to be checked. -/
public abbrev mkIso {R₁ R₂ : RingObjCat C} (e : R₁.X ≅ R₂.X)
    (one_f : η[R₁.X] ≫ e.hom = η[R₂.X] := by cat_disch)
    (mul_f : μ[R₁.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[R₂.X] := by cat_disch)
    (zero_f : ζ[R₁.X] ≫ e.hom = ζ[R₂.X] := by cat_disch)
    (add_f : σ[R₁.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ σ[R₂.X] := by cat_disch) : R₁ ≅ R₂ :=
  have : IsMonHom e.hom := ⟨one_f, mul_f⟩
  have : IsAddMonHom e.hom := ⟨zero_f, add_f⟩
  have : IsRingHom e.hom := ⟨⟩
  mkIso' e

end RingObjCat

namespace Functor

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable (F : C ⥤ D) [F.Braided]

/-- A lax braided functor carries a commutative additive monoid object to one: the additive
form of `CategoryTheory.Functor.isCommMonObj_obj`. -/
public instance isCommAddMonObjObj {M : C} [AddMonObj M] [IsCommAddMonObj M] :
    IsCommAddMonObj (F.obj M) where
  add_comm := by
    dsimp
    rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, IsCommAddMonObj.add_comm]

variable {R : C} [RingObj R]

private lemma delta_comp_add : δ F R R ≫ σ[F.obj R] = F.map σ[R] := by
  rw [Functor.obj.σ_def, Functor.Monoidal.δ_μ_assoc]

private lemma delta_whiskerLeft_add_mul :
    δ F R (R ⊗ R) ≫ (F.obj R ◁ δ F R R) ≫ (F.obj R ◁ σ[F.obj R]) ≫ μ[F.obj R] =
      F.map ((R ◁ σ[R]) ≫ μ[R]) := by
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, delta_comp_add, Functor.obj.μ_def,
    LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp]

private lemma delta_whiskerRight_add_mul :
    δ F (R ⊗ R) R ≫ (δ F R R ▷ F.obj R) ≫ (σ[F.obj R] ▷ F.obj R) ≫ μ[F.obj R] =
      F.map ((σ[R] ▷ R) ≫ μ[R]) := by
  rw [← MonoidalCategory.comp_whiskerRight_assoc, delta_comp_add, Functor.obj.μ_def,
    LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp]

@[reassoc]
private lemma delta_whiskerLeft_lift :
    δ F R (R ⊗ R) ≫ (F.obj R ◁ δ F R R) ≫
        lift ((F.obj R ◁ fst _ _) ≫ μ[F.obj R]) ((F.obj R ◁ snd _ _) ≫ μ[F.obj R]) =
      lift (F.map ((R ◁ fst _ _) ≫ μ[R])) (F.map ((R ◁ snd _ _) ≫ μ[R])) := by
  ext <;> simp only [Category.assoc, lift_fst, lift_snd, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Functor.OplaxMonoidal.δ_fst, Functor.OplaxMonoidal.δ_snd, Functor.obj.μ_def,
    LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp]

@[reassoc]
private lemma delta_whiskerRight_lift :
    δ F (R ⊗ R) R ≫ (δ F R R ▷ F.obj R) ≫
        lift ((fst _ _ ▷ F.obj R) ≫ μ[F.obj R]) ((snd _ _ ▷ F.obj R) ≫ μ[F.obj R]) =
      lift (F.map ((fst _ _ ▷ R) ≫ μ[R])) (F.map ((snd _ _ ▷ R) ≫ μ[R])) := by
  ext <;> simp only [Category.assoc, lift_fst, lift_snd, ← MonoidalCategory.comp_whiskerRight_assoc,
    Functor.OplaxMonoidal.δ_fst, Functor.OplaxMonoidal.δ_snd, Functor.obj.μ_def,
    LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.δ_μ_assoc, ← Functor.map_comp]

private lemma delta_whiskerLeft_lift_add :
    δ F R (R ⊗ R) ≫ (F.obj R ◁ δ F R R) ≫
        lift ((F.obj R ◁ fst _ _) ≫ μ[F.obj R]) ((F.obj R ◁ snd _ _) ≫ μ[F.obj R]) ≫
          σ[F.obj R] =
      F.map (lift ((R ◁ fst _ _) ≫ μ[R]) ((R ◁ snd _ _) ≫ μ[R]) ≫ σ[R]) := by
  rw [Functor.map_comp, ← Functor.Monoidal.lift_μ_assoc, ← delta_comp_add F,
    Functor.Monoidal.μ_δ_assoc, delta_whiskerLeft_lift_assoc]

private lemma delta_whiskerRight_lift_add :
    δ F (R ⊗ R) R ≫ (δ F R R ▷ F.obj R) ≫
        lift ((fst _ _ ▷ F.obj R) ≫ μ[F.obj R]) ((snd _ _ ▷ F.obj R) ≫ μ[F.obj R]) ≫
          σ[F.obj R] =
      F.map (lift ((fst _ _ ▷ R) ≫ μ[R]) ((snd _ _ ▷ R) ≫ μ[R]) ≫ σ[R]) := by
  rw [Functor.map_comp, ← Functor.Monoidal.lift_μ_assoc, ← delta_comp_add F,
    Functor.Monoidal.μ_δ_assoc, delta_whiskerRight_lift_assoc]

/-- **The image of a ring object under a braided functor is a ring object.** The additive group,
the commutativity of the addition and the multiplicative monoid are Mathlib's transports; each
distributivity identity is the functor applied to the identity below, with the comparison
isomorphism `δ` cancelled. -/
public abbrev ringObjObjOfBraided : RingObj (F.obj R) where
  __ := (inferInstance : AddGrpObj (F.obj R))
  __ := (inferInstance : IsCommAddMonObj (F.obj R))
  __ := (inferInstance : MonObj (F.obj R))
  mul_add := by
    have h : δ F R (R ⊗ R) ≫ (F.obj R ◁ δ F R R) ≫ ((F.obj R ◁ σ[F.obj R]) ≫ μ[F.obj R]) =
        δ F R (R ⊗ R) ≫ (F.obj R ◁ δ F R R) ≫
          (lift ((F.obj R ◁ fst _ _) ≫ μ[F.obj R]) ((F.obj R ◁ snd _ _) ≫ μ[F.obj R]) ≫
            σ[F.obj R]) := by
      rw [delta_whiskerLeft_add_mul, delta_whiskerLeft_lift_add, RingObj.mul_add]
    exact (cancel_epi (F.obj R ◁ δ F R R)).mp ((cancel_epi (δ F R (R ⊗ R))).mp h)
  add_mul := by
    have h : δ F (R ⊗ R) R ≫ (δ F R R ▷ F.obj R) ≫ ((σ[F.obj R] ▷ F.obj R) ≫ μ[F.obj R]) =
        δ F (R ⊗ R) R ≫ (δ F R R ▷ F.obj R) ≫
          (lift ((fst _ _ ▷ F.obj R) ≫ μ[F.obj R]) ((snd _ _ ▷ F.obj R) ≫ μ[F.obj R]) ≫
            σ[F.obj R]) := by
      rw [delta_whiskerRight_add_mul, delta_whiskerRight_lift_add, RingObj.add_mul]
    exact (cancel_epi (δ F R R ▷ F.obj R)).mp ((cancel_epi (δ F (R ⊗ R) R)).mp h)

section Map

/-- **A braided functor between cartesian monoidal categories takes ring objects to ring
objects**, as a functor. This is the ring analogue of `CategoryTheory.Functor.mapGrp`. -/
@[sga "4 IV 3.1.2" "special case"]
public def mapRing : RingObjCat C ⥤ RingObjCat D where
  obj A := letI := ringObjObjOfBraided F (R := A.X); { X := F.obj A.X }
  map {A B} f :=
    letI := ringObjObjOfBraided F (R := A.X)
    letI := ringObjObjOfBraided F (R := B.X)
    haveI : IsRingHom (F.map f.hom) := ⟨⟩
    { hom := F.map f.hom }
  map_id _ := RingObjCat.hom_ext (F.map_id _)
  map_comp _ _ := RingObjCat.hom_ext (F.map_comp _ _)

variable {F} {F' : C ⥤ D} [F'.Braided] {G : D ⥤ E} [G.Braided]

/-- Composing the unit comparisons of `F` and `G` is compatible with applying `G ∘ F` to `f`. -/
private lemma comp_epsilon_assoc {X : C} (f : 𝟙_ C ⟶ X) :
    (LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F)) ≫ G.map (F.map f) =
      LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F ≫ F.map f) := by
  simp

/-- Composing the tensorators of `F` and `G` is compatible with applying `G ∘ F` to `f`. -/
private lemma comp_mu_assoc {X : C} (f : X ⊗ X ⟶ X) :
    (LaxMonoidal.μ G _ _ ≫ G.map (LaxMonoidal.μ F X X)) ≫ G.map (F.map f) =
      LaxMonoidal.μ G _ _ ≫ G.map (LaxMonoidal.μ F X X ≫ F.map f) := by
  simp

/-- The unit of a composite acting on ring objects. -/
public lemma comp_mapRing_one (A : RingObjCat C) :
    η[((mapRing (F ⋙ G)).obj A).X] = η[((mapRing F ⋙ mapRing G).obj A).X] := by
  exact comp_epsilon_assoc _

/-- The multiplication of a composite acting on ring objects. -/
public lemma comp_mapRing_mul (A : RingObjCat C) :
    μ[((mapRing (F ⋙ G)).obj A).X] = μ[((mapRing F ⋙ mapRing G).obj A).X] := by
  exact comp_mu_assoc _

/-- The zero of a composite acting on ring objects. -/
public lemma comp_mapRing_zero (A : RingObjCat C) :
    ζ[((mapRing (F ⋙ G)).obj A).X] = ζ[((mapRing F ⋙ mapRing G).obj A).X] := by
  exact comp_epsilon_assoc _

/-- The addition of a composite acting on ring objects. -/
public lemma comp_mapRing_add (A : RingObjCat C) :
    σ[((mapRing (F ⋙ G)).obj A).X] = σ[((mapRing F ⋙ mapRing G).obj A).X] := by
  exact comp_mu_assoc _

/-- **A composite of braided functors acts on ring objects as the composite of their
actions.** -/
public def mapRingCompIso : mapRing (F ⋙ G) ≅ mapRing F ⋙ mapRing G :=
  NatIso.ofComponents
    (fun A ↦ RingObjCat.mkIso (.refl _)
      ((Category.comp_id _).trans (comp_mapRing_one A))
      (((Category.comp_id _).trans (comp_mapRing_mul A)).trans
        (((congrArg (fun t ↦ t ≫ μ[((mapRing F ⋙ mapRing G).obj A).X])
          (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.id_comp _)).symm))
      ((Category.comp_id _).trans (comp_mapRing_zero A))
      (((Category.comp_id _).trans (comp_mapRing_add A)).trans
        (((congrArg (fun t ↦ t ≫ σ[((mapRing F ⋙ mapRing G).obj A).X])
          (MonoidalCategory.id_tensorHom_id _ _)).trans (Category.id_comp _)).symm)))
    (fun {_ _} _ ↦ RingObjCat.hom_ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- In a cartesian monoidal category the tensorator is the product comparison, so every natural
transformation of monoidal functors is compatible with it. -/
public lemma natTrans_mu (e : F ⟶ F') (X Y : C) :
    (e.app X ⊗ₘ e.app Y) ≫ LaxMonoidal.μ F' X Y = LaxMonoidal.μ F X Y ≫ e.app (X ⊗ Y) := by
  rw [← cancel_mono (Functor.Monoidal.μIso F' X Y).inv]
  ext <;> simp

/-- In a cartesian monoidal category the unitor of a monoidal functor is the terminal
comparison, so every natural transformation of monoidal functors is compatible with it. -/
public lemma natTrans_epsilon (e : F ⟶ F') :
    LaxMonoidal.ε F ≫ e.app (𝟙_ C) = LaxMonoidal.ε F' := by
  rw [← cancel_mono (Functor.Monoidal.εIso F').inv]
  exact toUnit_unique _ _

/-- A natural transformation of braided functors respects the unit of the transported monoid
structure. -/
public lemma natTrans_one (e : F ⟶ F') (M : C) [MonObj M] :
    η[F.obj M] ≫ e.app M = η[F'.obj M] := by
  rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, e.naturality,
    ← Category.assoc, natTrans_epsilon e]

/-- A natural transformation of braided functors respects the multiplication of the transported
monoid structure. -/
public lemma natTrans_mul (e : F ⟶ F') (M : C) [MonObj M] :
    μ[F.obj M] ≫ e.app M = (e.app M ⊗ₘ e.app M) ≫ μ[F'.obj M] := by
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, e.naturality,
    ← Category.assoc, ← natTrans_mu e, Category.assoc]

/-- A natural transformation of braided functors respects the zero of the transported additive
monoid structure. -/
public lemma natTrans_zero (e : F ⟶ F') (M : C) [AddMonObj M] :
    ζ[F.obj M] ≫ e.app M = ζ[F'.obj M] := by
  rw [Functor.obj.ζ_def, Functor.obj.ζ_def, Category.assoc, e.naturality,
    ← Category.assoc, natTrans_epsilon e]

/-- A natural transformation of braided functors respects the addition of the transported
additive monoid structure. -/
public lemma natTrans_add (e : F ⟶ F') (M : C) [AddMonObj M] :
    σ[F.obj M] ≫ e.app M = (e.app M ⊗ₘ e.app M) ≫ σ[F'.obj M] := by
  rw [Functor.obj.σ_def, Functor.obj.σ_def, Category.assoc, e.naturality,
    ← Category.assoc, ← natTrans_mu e, Category.assoc]

/-- **A natural isomorphism of braided functors acts on ring objects.** -/
public def mapRingNatIso (e : F ≅ F') : mapRing F ≅ mapRing F' :=
  NatIso.ofComponents
    (fun A ↦ RingObjCat.mkIso (e.app A.X) (natTrans_one e.hom A.X) (natTrans_mul e.hom A.X)
      (natTrans_zero e.hom A.X) (natTrans_add e.hom A.X))
    (by intros; apply RingObjCat.hom_ext; exact e.hom.naturality _)

end Map

end Functor

end CategoryTheory

end
