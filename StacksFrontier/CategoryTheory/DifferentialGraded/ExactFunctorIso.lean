module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A functor of differential graded categories commuting with the shift up to isomorphism

Let `F : A ⟶ B` be a functor of differential graded categories over a commutative ring. The
hypothesis of Tag 0FQF, as `DGCategory.DGFunctor.CommShiftB` records it, is the *equality*
`F(x[n]) = F(x)[n]` of objects of `B` together with two heterogeneous equalities expressing
that `F` commutes with the shift of a homogeneous morphism and with the identifications
`Hom(x, y)[n] ≅ Hom(x, y[n])` of axiom (B).

That equality is too strong for the functors one wants to apply it to. For the differential
graded Yoneda functor `X ↦ h_X` of a differential graded category `C` carrying axiom (B), the
degree-`i` part of `h_{X[n]}` at an object `y` is `C.Hom y (X[n]) i` while that of `(h_X)[n]`
is `C.Hom y X (i + n)`, and axiom (B) relates the two by the linear equivalence
`DGCategory.ShiftAxiomB.toShift` and by nothing stronger. What is available there is an
*isomorphism* of right differential graded modules, not an equality.

This file is the isomorphism-valued variant of `DGCategory.DGFunctor.CommShiftB`: the comparison
`F(x[n]) ≅ F(x)[n]` is a closed degree-zero morphism of `B` with a closed degree-zero inverse,
that is, an isomorphism of `Comp(B)`, and the two heterogeneous equalities become equations in a
single Hom module of `B`, with the comparison inserted.

## Main definitions

* `DGCategory.DGFunctor.CommShiftBIso`: the isomorphism-valued hypothesis.
* `DGCategory.DGFunctor.CommShiftB.toCommShiftBIso`: the equality-valued hypothesis implies it,
  the comparison being the identity read along the equality of objects.
* `DGCategory.DGFunctor.CommShiftBIso.onKIso` and
  `DGCategory.DGFunctor.CommShiftBIso.kIso`: the resulting comparison isomorphism of functors
  on homotopy categories, for the differential graded shifts and for the translations axiom (B)
  puts on `K(A)` and `K(B)`.
* `DGCategory.DGFunctor.CommShiftBIso.mapTriangleK`: the induced functor on triangles.
* `DGCategory.DGFunctor.CommShiftKIso`: the same hypothesis together with the coherence of the
  comparison isomorphisms with the `ℤ`-action data of the translation functors.
* `DGCategory.DGFunctor.CommShiftK.toCommShiftKIso`: the same comparison of the two forms at
  that level, so that the exactness statement proved here subsumes the one proved for
  `DGCategory.DGFunctor.CommShiftK`.

## Main results

* `DGCategory.DGFunctor.CommShiftBIso.mapTriangleK_obj_associatedKTriangle`: the image of the
  triangle of an admissible short exact sequence is the triangle of the image sequence.
* `DGCategory.DGFunctor.CommShiftBIso.isDistinguishedTriangle_mapTriangleK`: the induced functor
  carries distinguished triangles to distinguished triangles. This is unconditional: no
  strictness of any kind is assumed, of `F` or of the two axiom (B) data.
* `DGCategory.DGFunctor.CommShiftKIso.isTriangulated`: the induced functor is an exact functor
  of triangulated categories, in the form of Mathlib's `Functor.CommShift` and
  `Functor.IsTriangulated`.

## Implementation notes

The comparison is asked for by its underlying cocycles rather than as a bundled isomorphism of
`Comp(B)`, because the two equations it has to satisfy are equations between homogeneous
morphisms of `B` and that is the form in which the concrete comparisons prove them. Passing to
homotopy classes is done once, in `DGCategory.DGFunctor.CommShiftBIso.onKIso`.

Mathlib's `Functor.CommShift` demands that the comparison isomorphisms agree with
`shiftFunctorZero` and `shiftFunctorAdd` of the two translations. For an equality-valued
comparison those agreements follow from the strictness of the translations,
`DGCategory.ShiftAxiomB.IsStrictKShift`, because then every isomorphism in sight is an
`eqToHom`. For an isomorphism-valued one they do not follow from anything: axiom (B) relates the
identifications `toShift n` for different `n` by no axiom whatever, so the comparison in degree
`0` and the composite of those in degrees `a` and `b` are unconstrained. They are therefore two
fields of `DGCategory.DGFunctor.CommShiftKIso`. Everything that does not go through
`Functor.CommShift` — that is, exactness in the encoding of Tag 09QW, where the distinguished
triangles are described by `DGCategory.IsDistinguishedTriangle` — is unconditional.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory
open CategoryTheory.Limits
open GradedSplitShortExact (connectingHom)

universe u v u' v' w

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R} {B : DGCategory.{v', u'} R}

/-- **The hypothesis of Tag 0FQF with the comparison an isomorphism.** Instead of the equality
`F(x[n]) = F(x)[n]` of objects of `B`, a closed degree-zero morphism between them with a closed
degree-zero inverse; and instead of the two heterogeneous equalities of
`DGCategory.DGFunctor.CommShiftB`, the corresponding equations with that comparison inserted,
which live in a single Hom module of `B`. -/
structure DGFunctor.CommShiftBIso (F : DGFunctor A B) (SA : ShiftAxiomBIso A)
    (SB : ShiftAxiomBIso B) where
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
  /-- The comparison is natural: `F(f[n])` followed by it is it followed by `F(f)[n]`. -/
  map : ∀ (n : ℤ) {x y : A.Obj} {k : ℤ} (f : A.Hom x y k),
    B.comp (zero_add k) (hom n y).1 (F.map ((SA.shiftFunctor n).map f)) =
      B.comp (add_zero k) ((SB.shiftFunctor n).map (F.map f)) (hom n x).1
  /-- The comparison carries the image of the identification of axiom (B) of `A` to the
  identification of axiom (B) of `B`. -/
  toShift : ∀ (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)),
    B.comp (zero_add k) (hom n y).1 (F.map (SA.toShift n x y k f)) =
      SB.toShift n (F.obj x) (F.obj y) k (F.map f)

namespace DGFunctor.CommShiftBIso

variable {F : DGFunctor A B} {SA : ShiftAxiomBIso A} {SB : ShiftAxiomBIso B}

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

/-- The commutation of `F` with the shift functors of axiom (B), as an isomorphism of functors
on homotopy categories. Its components are the homotopy classes of the comparison cocycles and
its naturality is the field `map` of the hypothesis. -/
def onKIso (hF : F.CommShiftBIso SA SB) (n : ℤ) :
    (SA.shiftFunctor n).onK ⋙ F.onK ≅ F.onK ⋙ (SB.shiftFunctor n).onK :=
  NatIso.ofComponents (hF.kIsoApp n) (by
    intro x y f
    induction f using Quotient.inductionOn with
    | _ f => exact congrArg (Quotient.mk _) (Subtype.ext (hF.map n f.1)))

/-- The component of `onKIso` at an object is the homotopy class of the comparison cocycle. -/
theorem onKIso_hom_app (hF : F.CommShiftBIso SA SB) (n : ℤ) (x : A.K) :
    (hF.onKIso n).hom.app x = hF.kHom n x :=
  rfl

/-- The same commutation isomorphism, written for the translation functors of `K(A)` and
`K(B)` supplied by axiom (B). -/
def kIso (hF : F.CommShiftBIso SA SB) (n : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    shiftFunctor A.K n ⋙ F.onK ≅ F.onK ⋙ shiftFunctor B.K n :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  Functor.isoWhiskerRight (eqToIso (SA.kShift_functor n)) F.onK ≪≫ hF.onKIso n ≪≫
    Functor.isoWhiskerLeft F.onK (eqToIso (SB.kShift_functor n)).symm

/-- The component of `kIso` at an object is the comparison `kHom` conjugated by the two
`eqToHom`s identifying the shift functors of axiom (B) with the translations. -/
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

/-- The functor on triangles induced by `F` and its commutation with the shift: the Mathlib
construction `Functor.mapTriangle` for the comparison isomorphism `kIso`. -/
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

/-- Let `m` be a morphism of `K(A)` into the shifted object of axiom (B) and let `mB` be the
image of `m` under `F` followed by the comparison `kHom`. Then the image of `m` followed by an
`eqToHom` to the translated object, followed by the comparison isomorphism `kIso`, is `mB`
followed by the corresponding `eqToHom`. -/
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
image sequence.** For an admissible short exact sequence `E`, the induced functor on triangles
sends the triangle of `E` to the triangle of `DGCategory.DGFunctor.mapGradedSplitShortExact E`.
-/
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
    rwa [← F.connectingHom_mapGradedSplitShortExact E] at h
  dsimp only [mapTriangleK, ShiftAxiomBIso.associatedKTriangle]
  congr 1
  refine hF.map_comp_kIso x z _ _ ?_ _ _
  exact congrArg (Quotient.mk _) hδ

/-- **Tag 0FQF for an isomorphism-valued comparison.** The functor induced by `F` on homotopy
categories carries the distinguished triangles of `K(A)` to the distinguished triangles of
`K(B)`, the third arrow of the image triangle being formed with the comparison isomorphism
`F(x[1]) ≅ F(x)[1]`. -/
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

/-- Any `Functor.CommShift ℤ` structure on the induced functor whose degree-one isomorphism is
the comparison isomorphism `kIso` makes that functor triangulated. -/
theorem onK_isTriangulated (CA : ConeSituationIso A) (CB : ConeSituationIso B)
    (hA : CA.shift.RoundTripCoherent) (hB : CB.shift.RoundTripCoherent)
    (hF : F.CommShiftBIso CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A CA n
    letI : Pretriangulated A.K := homotopyPretriangulatedIso A CA hA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObjectIso B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditiveIso B CB n
    letI : Pretriangulated B.K := homotopyPretriangulatedIso B CB hB
    ∀ hcs : F.onK.CommShift ℤ,
      letI := hcs
      F.onK.commShiftIso (1 : ℤ) = hF.kIso 1 → F.onK.IsTriangulated := by
  let : Preadditive A.K := homotopyPreadditive A
  let : HasZeroObject A.K := homotopyHasZeroObjectIso A CA
  let : HasShift A.K ℤ := CA.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A CA n
  let : Pretriangulated A.K := homotopyPretriangulatedIso A CA hA
  let : Preadditive B.K := homotopyPreadditive B
  let : HasZeroObject B.K := homotopyHasZeroObjectIso B CB
  let : HasShift B.K ℤ := CB.shift.kShift
  let : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditiveIso B CB n
  let : Pretriangulated B.K := homotopyPretriangulatedIso B CB hB
  intro hcs h1
  let := hcs
  have hdistA : Pretriangulated.distinguishedTriangles (C := A.K) =
      {U | IsDistinguishedTriangleIso A CA U} :=
    distinguishedTriangles_homotopyPretriangulatedIso A CA hA
  have hdistB : Pretriangulated.distinguishedTriangles (C := B.K) =
      {U | IsDistinguishedTriangleIso B CB U} :=
    distinguishedTriangles_homotopyPretriangulatedIso B CB hB
  refine ⟨fun T hT => ?_⟩
  rw [hdistA] at hT
  rw [hdistB]
  have heq : F.onK.mapTriangle.obj T = hF.mapTriangleK.obj T := by
    dsimp only [mapTriangleK]
    rw [← h1]
    rfl
  rw [heq]
  exact hF.isDistinguishedTriangle_mapTriangleK CA CB T hT

end DGFunctor.CommShiftBIso

/-- The isomorphism-valued hypothesis together with the coherence of the resulting family of
comparison isomorphisms with the `ℤ`-action data of the translation functors on the homotopy
categories. -/
structure DGFunctor.CommShiftKIso (F : DGFunctor A B) (SA : ShiftAxiomBIso A)
    (SB : ShiftAxiomBIso B) extends DGFunctor.CommShiftBIso F SA SB where
  /-- The comparison isomorphism in degree `0` is the canonical one. -/
  kIso_zero :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    toCommShiftBIso.kIso 0 = Functor.CommShift.isoZero F.onK ℤ
  /-- The comparison isomorphisms are additive in the degree. -/
  kIso_add : ∀ a b : ℤ,
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    toCommShiftBIso.kIso (a + b) =
      Functor.CommShift.isoAdd (toCommShiftBIso.kIso a) (toCommShiftBIso.kIso b)

namespace DGFunctor.CommShiftKIso

variable {F : DGFunctor A B} {SA : ShiftAxiomBIso A} {SB : ShiftAxiomBIso B}

/-- The induced functor `K(A) ⥤ K(B)` commutes with the translation functors. -/
@[instance_reducible]
def commShift (hF : F.CommShiftKIso SA SB) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    F.onK.CommShift ℤ :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  { commShiftIso := hF.toCommShiftBIso.kIso
    commShiftIso_zero := hF.kIso_zero
    commShiftIso_add := hF.kIso_add }

/-- **Tag 0FQF for an isomorphism-valued comparison.** A functor `F : A ⥤ B` of differential
graded categories over `R` between categories satisfying axioms (A), (B) and (C), which
commutes with the shift up to a closed degree-zero isomorphism, induces an exact functor
`K(A) ⥤ K(B)` of triangulated categories.

The commutation is asked for here as a `CommShiftKIso`, that is, together with the two
coherences of the comparison isomorphisms with the `ℤ`-action data of the translations. -/
@[sga "4 Vbis 2.5.1" "more general"]
theorem isTriangulated (CA : ConeSituationIso A) (CB : ConeSituationIso B)
    (hA : CA.shift.RoundTripCoherent) (hB : CB.shift.RoundTripCoherent)
    (hF : F.CommShiftKIso CA.shift CB.shift) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : HasZeroObject A.K := homotopyHasZeroObjectIso A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditiveIso A CA n
    letI : Pretriangulated A.K := homotopyPretriangulatedIso A CA hA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : HasZeroObject B.K := homotopyHasZeroObjectIso B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditiveIso B CB n
    letI : Pretriangulated B.K := homotopyPretriangulatedIso B CB hB
    letI : F.onK.CommShift ℤ := hF.commShift
    F.onK.IsTriangulated :=
  hF.toCommShiftBIso.onK_isTriangulated CA CB hA hB hF.commShift rfl

end DGFunctor.CommShiftKIso

namespace DGFunctor.CommShiftB

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- The identity cocycle read along an equality of objects. -/
def eqCocycle {b b' : B.Obj} (h : b = b') : B.Cocycle b b' :=
  Eq.ndrec (motive := fun c => B.Cocycle b c) ⟨B.id b, B.d_id b⟩ h

/-- The identity cocycle read along `h`, followed by the one read along `h.symm`, is the
identity cocycle. -/
theorem compCocycle_eqCocycle_symm {b b' : B.Obj} (h : b = b') :
    B.compCocycle (eqCocycle h.symm) (eqCocycle h) = ⟨B.id b, B.d_id b⟩ := by
  subst h
  exact Subtype.ext (B.id_comp (B.id b))

/-- The identity cocycle read along `h.symm`, followed by the one read along `h`, is the
identity cocycle. -/
theorem compCocycle_symm_eqCocycle {b b' : B.Obj} (h : b = b') :
    B.compCocycle (eqCocycle h) (eqCocycle h.symm) = ⟨B.id b', B.d_id b'⟩ :=
  compCocycle_eqCocycle_symm h.symm

/-- Two homogeneous morphisms that are heterogeneously equal along equalities `hb` and `hc` of
their targets and sources become equal after composing with the identity cocycles read along
`hb` and `hc`. -/
theorem comp_eqCocycle_eq {b₁ b₂ c₁ c₂ : B.Obj} (hb : b₁ = b₂) (hc : c₁ = c₂)
    {k : ℤ} (f : B.Hom c₁ b₁ k) (g : B.Hom c₂ b₂ k) (hfg : HEq f g) :
    B.comp (zero_add k) (eqCocycle hb).1 f = B.comp (add_zero k) g (eqCocycle hc).1 := by
  subst hb
  subst hc
  obtain rfl : f = g := eq_of_heq hfg
  rw [show (eqCocycle (rfl : b₁ = b₁)).1 = B.id b₁ from rfl,
    show (eqCocycle (rfl : c₁ = c₁)).1 = B.id c₁ from rfl, B.id_comp, B.comp_id]

/-- A homogeneous morphism heterogeneously equal to `g` along an equality `hb` of targets
becomes `g` after composing with the identity cocycle read along `hb`. -/
theorem comp_eqCocycle_eq_of_heq {b₁ b₂ c : B.Obj} (hb : b₁ = b₂) {k : ℤ}
    (f : B.Hom c b₁ k) (g : B.Hom c b₂ k) (hfg : HEq f g) :
    B.comp (zero_add k) (eqCocycle hb).1 f = g := by
  rw [comp_eqCocycle_eq hb rfl f g hfg]
  exact B.comp_id g

/-- **The equality-valued hypothesis is a special case of the isomorphism-valued one.** The
comparison is the identity of `F(x[n])`, read along the equality `F(x[n]) = F(x)[n]`; the two
heterogeneous equalities of `DGCategory.DGFunctor.CommShiftB` become, after substituting that
equality, the two equations of `DGCategory.DGFunctor.CommShiftBIso` with an identity inserted.
-/
def toCommShiftBIso (hF : F.CommShiftB SA SB) :
    F.CommShiftBIso SA.toShiftAxiomBIso SB.toShiftAxiomBIso where
  hom n x := eqCocycle (hF.obj n x)
  inv n x := eqCocycle (hF.obj n x).symm
  hom_inv_id n x := compCocycle_eqCocycle_symm (hF.obj n x)
  inv_hom_id n x := compCocycle_symm_eqCocycle (hF.obj n x)
  map n {x y} _ f := comp_eqCocycle_eq (hF.obj n y) (hF.obj n x) _ _ (hF.map n f)
  toShift n x y k f := comp_eqCocycle_eq_of_heq (hF.obj n y) _ _ (hF.toShift n x y k f)

/-- The homotopy class of the identity cocycle read along an equality of objects is the
`eqToHom` of that equality. -/
theorem mk_eqCocycle {b b' : B.K} (h : b = b') :
    (Quotient.mk (B.homotopySetoid (b : B.Obj) (b' : B.Obj)) (eqCocycle h) : b ⟶ b') =
      eqToHom h := by
  subst h
  rfl

/-- The comparison of `DGCategory.DGFunctor.CommShiftB.toCommShiftBIso` is the `eqToHom` of the
equality of objects, read in `K(B)`. -/
theorem kHom_toCommShiftBIso (hF : F.CommShiftB SA SB) (n : ℤ) (x : A.K) :
    hF.toCommShiftBIso.kHom n x = eqToHom (hF.objEqOnK n x) :=
  mk_eqCocycle (hF.objEqOnK n x)

/-- **The two comparison isomorphisms of functors agree.** The comparison isomorphism
`kIso` of `DGCategory.DGFunctor.CommShiftB.toCommShiftBIso` is that of the equality-valued
hypothesis. -/
theorem kIso_toCommShiftBIso (hF : F.CommShiftB SA SB) (n : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    hF.toCommShiftBIso.kIso n = hF.kIso n := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  rw [CommShiftBIso.kIso_hom_app, kHom_toCommShiftBIso, hF.kIso_hom_app n x, eqToHom_map,
    eqToHom_trans, eqToHom_trans]

end DGFunctor.CommShiftB

namespace DGFunctor.CommShiftK

variable {F : DGFunctor A B} {SA : ShiftAxiomB A} {SB : ShiftAxiomB B}

/-- **The equality-valued hypothesis with its two coherences is a special case of the
isomorphism-valued one with its two coherences.** Its comparison isomorphisms are those of
`DGCategory.DGFunctor.CommShiftB.toCommShiftBIso`. -/
def toCommShiftKIso (hF : F.CommShiftK SA SB) :
    F.CommShiftKIso SA.toShiftAxiomBIso SB.toShiftAxiomBIso where
  toCommShiftBIso := hF.toCommShiftB.toCommShiftBIso
  kIso_zero := by
    rw [CommShiftB.kIso_toCommShiftBIso]
    exact hF.kIso_zero
  kIso_add a b := by
    rw [CommShiftB.kIso_toCommShiftBIso, CommShiftB.kIso_toCommShiftBIso,
      CommShiftB.kIso_toCommShiftBIso]
    exact hF.kIso_add a b

end DGFunctor.CommShiftK

end DGCategory
