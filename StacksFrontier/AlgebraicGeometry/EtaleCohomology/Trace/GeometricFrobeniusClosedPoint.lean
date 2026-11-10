module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometric Frobenius at a closed point

Let `X` be a scheme and let `x` be a point of `X` whose residue field `κ(x)` is finite. The
geometric point at `x` is the one determined by an algebraic closure of `κ(x)` together with the
canonical morphism `Spec κ(x) ⟶ X`, and the geometric Frobenius of `κ(x)` — the inverse of the
arithmetic Frobenius `y ↦ y ^ #κ(x)` — is an endomorphism of that geometric point, hence acts on
the étale stalk there.

This is the construction for a rational point applied with base field `κ(x)` and rational point
`X.fromSpecResidueField x`; no new site machinery is needed.

## Main definitions

* `Stacks.Frobenius.geometricPointAt` is the geometric point at `x`.
* `Stacks.Frobenius.residueGeometricFrobenius` is the geometric Frobenius of an algebraic closure
  of `κ(x)` over `κ(x)`.
* `Stacks.Frobenius.frobeniusPointHom` exhibits it as an endomorphism of the geometric point.
* `Stacks.Frobenius.frobeniusStalkFunctor` and `Stacks.Frobenius.frobeniusStalk` are the induced
  endomorphisms of the étale stalk functor and of the stalk of a single sheaf.

## Main results

* `Stacks.Frobenius.frobeniusStalk_naturality`: the action is natural in the sheaf.
* `Stacks.Frobenius.frobeniusStalk_eq_geometricFrobeniusStalk`: at the canonical rational point
  of the residue field the construction is the geometric Frobenius for a rational point.
* `Stacks.Frobenius.frobeniusStalk_comm`: at a rational point `y` of a scheme over a finite field
  whose residue field has the same cardinality, a morphism of geometric points intertwines the
  two actions on stalks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Frobenius

section GeometricPointAt

/-- The geometric point of `X` at a point `x`: the geometric point over a rational point formed
with base field the residue field `κ(x)`, extension field an algebraic closure of `κ(x)`, and the
canonical morphism `Spec κ(x) ⟶ X`. -/
public abbrev geometricPointAt (X : Scheme.{u}) (x : X) : GeometricPoint X :=
  rationalGeometricPoint (k := X.residueField x) (AlgebraicClosure (X.residueField x))
    (X.fromSpecResidueField x)

/-- The geometric point at `x` lies over `x`. -/
public lemma geometricPointAt_liesOver (X : Scheme.{u}) (x : X) :
    (geometricPointAt X x).LiesOver x := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x) default = x
  exact X.fromSpecResidueField_apply x _

/-- The geometric Frobenius of an algebraic closure of a finite residue field `κ(x)` over `κ(x)`:
the inverse of the arithmetic Frobenius `y ↦ y ^ #κ(x)`. -/
@[sga "7 I 6.3", sga "7 XXI 2.0", sga "7 XXI 5.0" "more general", sga "7 XXII 2.2.4"]
public def residueGeometricFrobenius (X : Scheme.{u}) (x : X) [Finite (X.residueField x)] :
    AlgebraicClosure (X.residueField x) ≃ₐ[X.residueField x]
      AlgebraicClosure (X.residueField x) :=
  letI : Fintype (X.residueField x) := Fintype.ofFinite _
  haveI : Fact (ringChar (X.residueField x)).Prime :=
    ⟨CharP.char_is_prime (X.residueField x) (ringChar (X.residueField x))⟩
  (arithmeticFrobenius (X.residueField x) (AlgebraicClosure (X.residueField x))
      (ringChar (X.residueField x))
      (FiniteField.card (X.residueField x) (ringChar (X.residueField x))).choose
      (FiniteField.card (X.residueField x) (ringChar (X.residueField x))).choose_spec.2).symm

/-- The inverse of the geometric Frobenius at `x` raises to the power the cardinality of the
residue field. -/
public lemma residueGeometricFrobenius_symm_apply (X : Scheme.{u}) (x : X)
    [Finite (X.residueField x)] (y : AlgebraicClosure (X.residueField x)) :
    (residueGeometricFrobenius X x).symm y = y ^ Nat.card (X.residueField x) := by
  rw [residueGeometricFrobenius, AlgEquiv.symm_symm, arithmeticFrobenius_apply]
  exact congrArg (y ^ ·) (@Nat.card_eq_fintype_card _ (Fintype.ofFinite _)).symm

/-- The geometric Frobenius at a point with finite residue field, as an endomorphism of the
geometric point there. -/
@[sga "7 XXI 5.0"]
public def frobeniusPointHom (X : Scheme.{u}) (x : X) [Finite (X.residueField x)] :
    GeometricPoint.Hom (geometricPointAt X x) (geometricPointAt X x) :=
  galoisPointHom (AlgebraicClosure (X.residueField x)) (residueGeometricFrobenius X x)
    (X.fromSpecResidueField x)

/-- The underlying scheme morphism of `frobeniusPointHom X x` is `Spec` of the geometric Frobenius
`residueGeometricFrobenius X x`. -/
@[simp]
public lemma frobeniusPointHom_hom (X : Scheme.{u}) (x : X) [Finite (X.residueField x)] :
    (frobeniusPointHom X x).hom =
      Spec.map (CommRingCat.ofHom (residueGeometricFrobenius X x).toAlgHom.toRingHom) :=
  rfl

end GeometricPointAt

section FrobeniusStalk

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] (X : Scheme.{u}) (x : X)
  [Finite (X.residueField x)]

/-- The geometric Frobenius at a point with finite residue field, as an endomorphism of the étale
stalk functor at the geometric point there. -/
@[sga "4½ Rapport 1.5"]
public def frobeniusStalkFunctor :
    (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber (A := A) ⟶
      (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber :=
  galoisStalkAction A (AlgebraicClosure (X.residueField x)) (residueGeometricFrobenius X x)
    (X.fromSpecResidueField x)

/-- The geometric Frobenius at a point with finite residue field, acting on the étale stalk of a
sheaf there. -/
public def frobeniusStalk (F : Sheaf X.smallEtaleTopology A) :
    (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber.obj F ⟶
      (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber.obj F :=
  (frobeniusStalkFunctor A X x).app F

/-- The action on the stalk of a sheaf is the component there of the action on the stalk
functor. -/
public lemma frobeniusStalk_eq_galoisStalkAction_app (F : Sheaf X.smallEtaleTopology A) :
    frobeniusStalk A X x F =
      (galoisStalkAction A (AlgebraicClosure (X.residueField x)) (residueGeometricFrobenius X x)
        (X.fromSpecResidueField x)).app F :=
  rfl

/-- The geometric Frobenius at a point is natural in the sheaf. -/
public lemma frobeniusStalk_naturality {F G : Sheaf X.smallEtaleTopology A} (α : F ⟶ G) :
    (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber.map α ≫
        frobeniusStalk A X x G =
      frobeniusStalk A X x F ≫
        (Scheme.pointSmallEtale (geometricPointAt X x).hom).sheafFiber.map α :=
  (frobeniusStalkFunctor A X x).naturality α

end FrobeniusStalk

section Compare

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A] (X : Scheme.{u}) (x : X)

/-- At the canonical rational point of a point with finite residue field, the geometric Frobenius
there is the geometric Frobenius for a rational point, as endomorphisms of the stalk functor. -/
public lemma frobeniusStalkFunctor_eq_geometricFrobeniusStalkFunctor
    [Fintype (X.residueField x)] (p f : ℕ) [Fact p.Prime]
    [CharP (AlgebraicClosure (X.residueField x)) p]
    (hcard : Fintype.card (X.residueField x) = p ^ f) :
    frobeniusStalkFunctor A X x =
      geometricFrobeniusStalkFunctor A (AlgebraicClosure (X.residueField x)) p f hcard
        (X.fromSpecResidueField x) := by
  rw [geometricFrobeniusStalkFunctor_eq A (AlgebraicClosure (X.residueField x)) p f hcard
      (X.fromSpecResidueField x) (residueGeometricFrobenius X x).symm
      (fun y => by rw [residueGeometricFrobenius_symm_apply, Nat.card_eq_fintype_card]),
    AlgEquiv.symm_symm]
  rfl

/-- At the canonical rational point of a point with finite residue field, the geometric Frobenius
there is the geometric Frobenius for a rational point, acting on the stalk of a sheaf. -/
public lemma frobeniusStalk_eq_geometricFrobeniusStalk [Fintype (X.residueField x)]
    (p f : ℕ) [Fact p.Prime] [CharP (AlgebraicClosure (X.residueField x)) p]
    (hcard : Fintype.card (X.residueField x) = p ^ f) (F : Sheaf X.smallEtaleTopology A) :
    frobeniusStalk A X x F =
      geometricFrobeniusStalk A (AlgebraicClosure (X.residueField x)) p f hcard
        (X.fromSpecResidueField x) F :=
  NatTrans.congr_app
    (frobeniusStalkFunctor_eq_geometricFrobeniusStalkFunctor A X x p f hcard) F

variable [Finite (X.residueField x)] {k : Type u} [Field k] [Fintype k] (K : Type u) [Field K]
  [IsAlgClosed K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP K p]

/-- At a rational point `y` of a scheme over a finite field `k` whose residue field at `x` has
`#k` elements, a morphism of geometric points from the geometric point at `x` to the geometric
point over `y` intertwines the two geometric Frobenius actions on the stalk functors. -/
public lemma frobeniusStalkFunctor_comm (hcard : Fintype.card k = p ^ f) (y : Spec (.of k) ⟶ X)
    (θ : GeometricPoint.Hom (geometricPointAt X x) (rationalGeometricPoint K y))
    (hres : Nat.card (X.residueField x) = Fintype.card k) :
    GrothendieckTopology.Point.Hom.sheafFiber (A := A) (smallEtalePointHom X θ) ≫
        frobeniusStalkFunctor A X x =
      geometricFrobeniusStalkFunctor A K p f hcard y ≫
        GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X θ) := by
  obtain ⟨φ, hθ⟩ : ∃ φ : K →+* AlgebraicClosure (X.residueField x),
      θ.hom = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage θ.hom).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have key : ∀ z : K, (residueGeometricFrobenius X x) (φ z) =
      φ ((arithmeticFrobenius k K p f hcard).symm z) := by
    intro z
    refine (residueGeometricFrobenius X x).symm.injective ?_
    rw [AlgEquiv.symm_apply_apply, residueGeometricFrobenius_symm_apply, hres, ← map_pow]
    congr 1
    rw [← arithmeticFrobenius_apply k K p f hcard, AlgEquiv.apply_symm_apply]
  have hring : CommRingCat.ofHom φ ≫
      CommRingCat.ofHom (residueGeometricFrobenius X x).toAlgHom.toRingHom =
    CommRingCat.ofHom (arithmeticFrobenius k K p f hcard).symm.toAlgHom.toRingHom ≫
      CommRingCat.ofHom φ := by
    ext z
    exact key z
  have ha : (frobeniusPointHom X x).hom ≫ θ.hom =
      θ.hom ≫ (galoisPointHom K (arithmeticFrobenius k K p f hcard).symm y).hom := by
    rw [frobeniusPointHom_hom, galoisPointHom_hom, hθ, ← Spec.map_comp, ← Spec.map_comp, hring]
  let c : GeometricPoint.Hom (geometricPointAt X x) (rationalGeometricPoint K y) :=
    ⟨(frobeniusPointHom X x).hom ≫ θ.hom, by
      rw [Category.assoc, θ.comm, (frobeniusPointHom X x).comm]⟩
  simp only [frobeniusStalkFunctor, geometricFrobeniusStalkFunctor, galoisStalkAction]
  erw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
    ← GrothendieckTopology.Point.Hom.sheafFiber_comp,
    ← smallEtalePointHom_comp (frobeniusPointHom X x) θ c rfl,
    ← smallEtalePointHom_comp θ _ c ha]

/-- The stalkwise form of `frobeniusStalkFunctor_comm`. -/
public lemma frobeniusStalk_comm (hcard : Fintype.card k = p ^ f) (y : Spec (.of k) ⟶ X)
    (θ : GeometricPoint.Hom (geometricPointAt X x) (rationalGeometricPoint K y))
    (hres : Nat.card (X.residueField x) = Fintype.card k)
    (F : Sheaf X.smallEtaleTopology A) :
    (GrothendieckTopology.Point.Hom.sheafFiber (A := A) (smallEtalePointHom X θ)).app F ≫
        frobeniusStalk A X x F =
      geometricFrobeniusStalk A K p f hcard y F ≫
        (GrothendieckTopology.Point.Hom.sheafFiber (A := A) (smallEtalePointHom X θ)).app F :=
  NatTrans.congr_app (frobeniusStalkFunctor_comm A X x K p f hcard y θ hres) F

end Compare

end Stacks.Frobenius

end
