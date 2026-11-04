module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctorIso

/-!
# Additive functors of differential graded categories over two rings

A `DGCategory.DGFunctor` relates two differential graded categories over *one* commutative ring.
A functor between the categories of differential graded modules over two different ringed sites —
the direct image of [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS), say — is
linear over neither ring of global sections in a way that relates them, but it is additive, and
additivity is all that the exactness argument of [Stacks, Tag 0FQF] uses. This file records a
functor between differential graded categories over two rings which preserves the grading, the
differential, composition, identities and sums, and proves for it the exactness statement of
Tag 0FQF with the comparison `F(x[n]) ≅ F(x)[n]` an isomorphism.

## Main definitions

* `DGCategory.AddDGFunctor`: an additive functor of differential graded categories, the two
  categories being linear over two possibly different commutative rings.
* `DGCategory.AddDGFunctor.onK`: the induced functor on homotopy categories.
* `DGCategory.AddDGFunctor.mapGradedSplitShortExact`: the image of an admissible short exact
  sequence.
* `DGCategory.AddDGFunctor.CommShiftBIso`: the hypothesis of Tag 0FQF with the comparison
  `F(x[n]) ≅ F(x)[n]` an isomorphism, and `DGCategory.AddDGFunctor.CommShiftBIso.kIso` the
  resulting comparison of functors on homotopy categories.

## Main results

* `DGCategory.AddDGFunctor.CommShiftBIso.isDistinguishedTriangle_mapTriangleK`: the induced
  functor carries distinguished triangles to distinguished triangles.
* `DGCategory.AddDGFunctor.CommShiftBIso.onK_isTriangulated`: so any `Functor.CommShift ℤ` of
  the induced functor whose degree-one isomorphism is the comparison makes it triangulated.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory CategoryTheory.Limits
open GradedSplitShortExact (connectingHom)

universe u v u' v' w w'

variable {R₁ : Type w} [CommRing R₁] {R₂ : Type w'} [CommRing R₂]
  {A : DGCategory.{v, u} R₁} {B : DGCategory.{v', u'} R₂}

/-- **An additive functor of differential graded categories**, the two categories being linear
over two possibly different commutative rings: a map on objects together with maps of degree
zero on Hom modules which are additive and commute with the differential, composition and
identities. -/
structure AddDGFunctor (A : DGCategory.{v, u} R₁) (B : DGCategory.{v', u'} R₂) where
  /-- The map on objects. -/
  obj : A.Obj → B.Obj
  /-- The degree-preserving map on Hom modules. -/
  map : ∀ {x y : A.Obj} {n : ℤ}, A.Hom x y n → B.Hom (obj x) (obj y) n
  /-- It is additive. -/
  map_add : ∀ {x y : A.Obj} {n : ℤ} (f g : A.Hom x y n), map (f + g) = map f + map g
  /-- It commutes with the differential. -/
  map_d : ∀ {x y : A.Obj} {n : ℤ} (f : A.Hom x y n), map (A.d f) = B.d (map f)
  /-- It preserves composition. -/
  map_comp : ∀ {x y z : A.Obj} {m n k : ℤ} (h : m + n = k) (g : A.Hom y z m) (f : A.Hom x y n),
    map (A.comp h g f) = B.comp h (map g) (map f)
  /-- It preserves identities. -/
  map_id : ∀ x : A.Obj, map (A.id x) = B.id (obj x)

namespace AddDGFunctor

variable (F : AddDGFunctor A B)

/-- An additive functor of differential graded categories preserves zero morphisms. -/
theorem map_zero {x y : A.Obj} {n : ℤ} : F.map (0 : A.Hom x y n) = 0 := by
  have := F.map_add (0 : A.Hom x y n) 0; simpa using this.symm

/-- An additive functor of differential graded categories preserves differences. -/
theorem map_sub {x y : A.Obj} {n : ℤ} (f g : A.Hom x y n) : F.map (f - g) = F.map f - F.map g :=
  eq_sub_of_add_eq (by rw [← F.map_add, sub_add_cancel])

/-- An additive functor of differential graded categories commutes with the differential
`d'`, whose target degree is given by an equation. -/
theorem map_d' {x y : A.Obj} {n m : ℤ} (h : n + 1 = m) (f : A.Hom x y n) :
    F.map (A.d' h f) = B.d' h (F.map f) := by
  subst h
  exact F.map_d f

/-- The image of a cocycle is a cocycle. -/
theorem map_cocycle {x y : A.Obj} (f : A.Cocycle x y) : B.d (F.map f.1) = 0 := by
  rw [← F.map_d, f.2, F.map_zero]

/-- The cocycle `F.map f` for a cocycle `f`. -/
def mapCocycle {x y : A.Obj} (f : A.Cocycle x y) : B.Cocycle (F.obj x) (F.obj y) :=
  ⟨F.map f.1, F.map_cocycle f⟩

/-- The induced map on homotopy classes. -/
def mapHomotopyClass {x y : A.Obj} (f : A.HomotopyClass x y) :
    B.HomotopyClass (F.obj x) (F.obj y) :=
  Quotient.map (fun f => F.mapCocycle f)
    (fun f₁ f₂ hf => by
      obtain ⟨h, hh⟩ := hf
      refine ⟨F.map h, ?_⟩
      change F.map f₁.1 - F.map f₂.1 = _
      rw [← F.map_sub, hh, F.map_d']) f

/-- The induced functor on homotopy categories. -/
def onK : A.K ⥤ B.K where
  obj x := F.obj x
  map f := F.mapHomotopyClass f
  map_id x := congrArg (Quotient.mk _) (Subtype.ext (F.map_id x))
  map_comp {x y z} f g := by
    refine Quotient.inductionOn₂ f g (fun f g => ?_)
    exact congrArg (Quotient.mk _) (Subtype.ext (F.map_comp _ g.1 f.1))

/-- The induced functor on homotopy categories sends the class of a cocycle `f` to the class of
`F.map f`. -/
theorem onK_map_mk {x y : A.Obj} (f : A.Cocycle x y) :
    F.onK.map (X := x) (Y := y) (Quotient.mk _ f) = Quotient.mk _ (F.mapCocycle f) := rfl

/-- The image of an admissible short exact sequence with a chosen graded splitting. -/
def mapGradedSplitShortExact {x y z : A.Obj} (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact (A := B) (F.obj x) (F.obj y) (F.obj z) where
  a := F.mapCocycle E.a
  b := F.mapCocycle E.b
  π := F.map E.π
  s := F.map E.s
  π_a := by
    simp only [mapCocycle]
    rw [← F.map_comp, E.π_a, F.map_id]
  b_s := by
    simp only [mapCocycle]
    rw [← F.map_comp, E.b_s, F.map_id]
  π_s := by rw [← F.map_comp, E.π_s, F.map_zero]
  a_π_add_s_b := by
    simp only [mapCocycle]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, E.a_π_add_s_b, F.map_id]

/-- The connecting morphism of the image sequence is the image of the connecting morphism. -/
theorem connectingHom_mapGradedSplitShortExact {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    GradedSplitShortExact.connectingHom (F.mapGradedSplitShortExact E) =
      F.map (GradedSplitShortExact.connectingHom E) := by
  simp only [GradedSplitShortExact.connectingHom, mapGradedSplitShortExact]
  rw [F.map_comp, F.map_d]

/-- **The hypothesis of Tag 0FQF with the comparison an isomorphism**, for an additive
functor. -/
structure CommShiftBIso (SA : ShiftAxiomBIso A) (SB : ShiftAxiomBIso B) where
  /-- The comparison `F(x[n]) ⟶ F(x)[n]`, a closed degree-zero morphism of `B`. -/
  hom : ∀ (n : ℤ) (x : A.Obj),
    B.Cocycle (F.obj ((SA.shiftFunctor n).obj x)) ((SB.shiftFunctor n).obj (F.obj x))
  /-- Its inverse, again closed of degree zero. -/
  inv : ∀ (n : ℤ) (x : A.Obj),
    B.Cocycle ((SB.shiftFunctor n).obj (F.obj x)) (F.obj ((SA.shiftFunctor n).obj x))
  /-- The comparison followed by its inverse is the identity. -/
  hom_inv_id : ∀ (n : ℤ) (x : A.Obj),
    B.compCocycle (inv n x) (hom n x) =
      ⟨B.id (F.obj ((SA.shiftFunctor n).obj x)), B.d_id _⟩
  /-- Its inverse followed by the comparison is the identity. -/
  inv_hom_id : ∀ (n : ℤ) (x : A.Obj),
    B.compCocycle (hom n x) (inv n x) =
      ⟨B.id ((SB.shiftFunctor n).obj (F.obj x)), B.d_id _⟩
  /-- The comparison is natural. -/
  map : ∀ (n : ℤ) {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    B.comp (zero_add k) (hom n y).1 (F.map ((SA.shiftFunctor n).map f)) =
      B.comp (add_zero k) ((SB.shiftFunctor n).map (F.map f)) (hom n x).1
  /-- The comparison carries the identification of axiom (B) of `A` to that of `B`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)),
    B.comp (zero_add k) (hom n y).1 (F.map (SA.toShift n x y k f)) =
      SB.toShift n (F.obj x) (F.obj y) k (F.map f)

namespace CommShiftBIso

variable {F} {SA : ShiftAxiomBIso A} {SB : ShiftAxiomBIso B}

/-- The comparison, as a morphism of `K(B)`. -/
def kHom (hF : F.CommShiftBIso SA SB) (n : ℤ) (x : A.K) :
    F.onK.obj ((SA.shiftFunctor n).onK.obj x) ⟶ (SB.shiftFunctor n).onK.obj (F.onK.obj x) :=
  Quotient.mk (B.homotopySetoid _ _) (hF.hom n (x : A.Obj))

/-- The comparison at one object, as an isomorphism of `K(B)`. -/
def kIsoApp (hF : F.CommShiftBIso SA SB) (n : ℤ) (x : A.K) :
    ((SA.shiftFunctor n).onK ⋙ F.onK).obj x ≅ (F.onK ⋙ (SB.shiftFunctor n).onK).obj x where
  hom := hF.kHom n x
  inv := Quotient.mk (B.homotopySetoid _ _) (hF.inv n (x : A.Obj))
  hom_inv_id := congrArg (Quotient.mk _) (hF.hom_inv_id n (x : A.Obj))
  inv_hom_id := congrArg (Quotient.mk _) (hF.inv_hom_id n (x : A.Obj))

/-- The commutation of `F` with the shift functors of axiom (B), on homotopy categories. -/
def onKIso (hF : F.CommShiftBIso SA SB) (n : ℤ) :
    (SA.shiftFunctor n).onK ⋙ F.onK ≅ F.onK ⋙ (SB.shiftFunctor n).onK :=
  NatIso.ofComponents (hF.kIsoApp n) (by
    intro x y f
    induction f using Quotient.inductionOn with
    | _ f => exact congrArg (Quotient.mk _) (Subtype.ext (hF.map n f.1)))

/-- The component of `onKIso` at `x` is the comparison `kHom` at `x`. -/
theorem onKIso_hom_app (hF : F.CommShiftBIso SA SB) (n : ℤ) (x : A.K) :
    (hF.onKIso n).hom.app x = hF.kHom n x :=
  rfl

/-- The same commutation isomorphism, for the translation functors of `K(A)` and `K(B)`. -/
def kIso (hF : F.CommShiftBIso SA SB) (n : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    shiftFunctor A.K n ⋙ F.onK ≅ F.onK ⋙ shiftFunctor B.K n :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  Functor.isoWhiskerRight (eqToIso (SA.kShift_functor n)) F.onK ≪≫ hF.onKIso n ≪≫
    Functor.isoWhiskerLeft F.onK (eqToIso (SB.kShift_functor n)).symm

/-- The component of `kIso` at `x` is the comparison `kHom` at `x`, conjugated by the
identifications of the translation functors with the shift functors of axiom (B). -/
theorem kIso_hom_app (hF : F.CommShiftBIso SA SB) (n : ℤ) (x : A.K) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    (hF.kIso n).hom.app x =
      F.onK.map (eqToHom (Functor.congr_obj (SA.kShift_functor n) x)) ≫
        hF.kHom n x ≫
          eqToHom (Functor.congr_obj (SB.kShift_functor n) (F.onK.obj x)).symm := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  simp only [kIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToHom_app, eqToIso.hom, eqToIso.inv, onKIso_hom_app]

/-- The functor on triangles induced by `F` and its commutation with the shift. -/
def mapTriangleK (hF : F.CommShiftBIso SA SB) :
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

private theorem map_comp_kIso (hF : F.CommShiftBIso SA SB) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    ∀ (x₀ zz : A.K) (m : zz ⟶ (SA.shiftFunctor 1).onK.obj x₀)
      (mB : F.onK.obj zz ⟶ (SB.shiftFunctor 1).onK.obj (F.onK.obj x₀)),
      F.onK.map m ≫ hF.kHom 1 x₀ = mB →
      ∀ (p : (SA.shiftFunctor 1).onK.obj x₀ = (shiftFunctor A.K 1).obj x₀)
        (q : (SB.shiftFunctor 1).onK.obj (F.onK.obj x₀) =
          (shiftFunctor B.K 1).obj (F.onK.obj x₀)),
        F.onK.map (m ≫ eqToHom p) ≫ (hF.kIso 1).hom.app x₀ = mB ≫ eqToHom q := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  intro x₀ zz m mB hm p q
  rw [Functor.map_comp, eqToHom_map, hF.kIso_hom_app 1 x₀, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Category.assoc, hm]

/-- **The image of the triangle of an admissible short exact sequence is the triangle of the
image sequence.** -/
theorem mapTriangleK_obj_associatedKTriangle (hF : F.CommShiftBIso SA SB) {x y z : A.Obj}
    (E : GradedSplitShortExact (A := A) x y z) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    hF.mapTriangleK.obj (SA.associatedKTriangle E) =
      SB.associatedKTriangle (F.mapGradedSplitShortExact E) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  have hδ : B.compCocycle (hF.hom 1 x) (F.mapCocycle (SA.connectingCocycle E)) =
      SB.connectingCocycle (F.mapGradedSplitShortExact E) := by
    refine Subtype.ext ?_
    have h := hF.toShift 1 z x 0 (connectingHom E)
    rw [← F.connectingHom_mapGradedSplitShortExact E] at h
    exact h
  dsimp only [mapTriangleK, ShiftAxiomBIso.associatedKTriangle]
  congr 1
  refine hF.map_comp_kIso x z _ _ ?_ _ _
  exact congrArg (Quotient.mk _) hδ

/-- **Tag 0FQF for an additive functor with an isomorphism-valued comparison.** The induced
functor carries distinguished triangles to distinguished triangles. -/
theorem isDistinguishedTriangle_mapTriangleK (CA : ConeSituationIso A) (CB : ConeSituationIso B)
    (hF : F.CommShiftBIso CA.shift CB.shift) :
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : HasShift B.K ℤ := CB.shift.kShift
    ∀ T : Pretriangulated.Triangle A.K, IsDistinguishedTriangleIso A CA T →
      IsDistinguishedTriangleIso B CB (hF.mapTriangleK.obj T) := by
  let : HasShift A.K ℤ := CA.shift.kShift
  let : HasShift B.K ℤ := CB.shift.kShift
  intro T hT
  obtain ⟨x, y, z, E, ⟨φ⟩⟩ := hT
  exact ⟨F.obj x, F.obj y, F.obj z, F.mapGradedSplitShortExact E,
    ⟨(hF.mapTriangleK.mapIso φ).trans
      (eqToIso (hF.mapTriangleK_obj_associatedKTriangle E))⟩⟩

/-- Any `Functor.CommShift ℤ` of the induced functor whose degree-one isomorphism is the
comparison `kIso 1` makes that functor triangulated, for strict cone situations on both sides. -/
theorem onK_isTriangulated (CA : ConeSituation A) (CB : ConeSituation B)
    (hF : F.CommShiftBIso CA.shift.toShiftAxiomBIso CB.shift.toShiftAxiomBIso) :
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
      {U | IsDistinguishedTriangleIso A CA.toConeSituationIso U} :=
    distinguishedTriangles_homotopyPretriangulatedIso A CA.toConeSituationIso
      CA.shift.roundTripCoherent
  have hdistB : Pretriangulated.distinguishedTriangles (C := B.K) =
      {U | IsDistinguishedTriangleIso B CB.toConeSituationIso U} :=
    distinguishedTriangles_homotopyPretriangulatedIso B CB.toConeSituationIso
      CB.shift.roundTripCoherent
  refine ⟨fun T hT => ?_⟩
  rw [hdistA] at hT
  rw [hdistB]
  have heq : F.onK.mapTriangle.obj T = hF.mapTriangleK.obj T := by
    dsimp only [mapTriangleK]
    rw [← h1]
    rfl
  rw [heq]
  exact hF.isDistinguishedTriangle_mapTriangleK CA.toConeSituationIso CB.toConeSituationIso T hT

end CommShiftBIso

end AddDGFunctor

end DGCategory
