module

public import StacksFrontier.Homology.Tor.GradedAlgebra.Existence

/-!
# The graded Tor algebra: canonical structure and functoriality

The canonical graded Tor algebra `GradedTor.canonicalAlgebra`, the graded algebra maps
`GradedTor.canonicalMap` induced by `R`-algebra maps, and the functorial system
`GradedTor.canonical` with its uniqueness.
-/

universe u uR uA v

@[expose] public noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace GradedTor

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]

/-- The canonical graded Tor algebra attached to `B`: the unique unital associative graded algebra
structure whose multiplication is the Tor multiplication. -/
@[sga "6 VII 2.1" "partial"]
public noncomputable def canonicalAlgebra (B : AlgCat.{v, uR} R) :
    Algebra.{uR, uA, v} R A B :=
  (existsUnique_algebra.{uR, uA, v} R A B).exists.choose

/-- The prescribed multiplication uniquely determines the graded algebra structure,
independently of all construction choices. -/
public theorem canonicalAlgebra_unique (B : AlgCat.{v, uR} R)
    (X : Algebra.{uR, uA, v} R A B) : X = canonicalAlgebra.{uR, uA, v} R A B :=
  (existsUnique_algebra.{uR, uA, v} R A B).unique trivial trivial

/-- Multiplication in the canonical graded Tor algebra is the Tor cross product followed by the
map on Tor induced by multiplication on `B`. -/
@[sga "6 VII 2.1" "partial"]
public lemma canonical_mul_ofNat (B : AlgCat.{v, uR} R) (n m : ℕ) :
    (canonicalAlgebra.{uR, uA, v} R A B).mul n m = torMultiplication.{uR, uA, v} R A B n m :=
  (canonicalAlgebra.{uR, uA, v} R A B).mul_ofNat n m

end GradedTor

end

noncomputable section

open CategoryTheory CochainComplex.DerivedTensor
open scoped ChangeOfRings

namespace GradedTor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]

omit [CommRing A] [_root_.Algebra R A] in
private lemma liftedMap_mul {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    TorCrossProduct.moduleTensorMap.{max uR uA v, uR}
        (M := GradedTor.liftedModule R A B) (M' := GradedTor.liftedModule R A C)
        (N := GradedTor.liftedModule R A B) (N' := GradedTor.liftedModule R A C)
        (ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap)
        (ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap) ≫
      ModuleCat.ofHom (TensorProduct.lift
        (LinearMap.mul R (GradedTor.liftedAlgebra R A C))) =
      ModuleCat.ofHom (TensorProduct.lift
        (LinearMap.mul R (GradedTor.liftedAlgebra R A B))) ≫
      ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  exact (map_mul (GradedTor.liftedMap R A g).hom x y).symm

@[sga "6 VII 2.1" "partial"]
private lemma map_torMultiplication {B C : AlgCat.{v, uR} R} (g : B ⟶ C)
    (n m : ℕ) :
    GradedTor.torMultiplication R A B n m ≫
        GradedTor.torPieceMap R A g (n + m) =
      TorCrossProduct.moduleTensorMap.{max uR uA v, uA}
          (M := GradedTor.torPiece R A B n) (M' := GradedTor.torPiece R A C n)
          (N := GradedTor.torPiece R A B m) (N' := GradedTor.torPiece R A C m)
          (GradedTor.torPieceMap R A g n) (GradedTor.torPieceMap R A g m) ≫
        GradedTor.torMultiplication R A C n m := by
  change _ ≫ (RingTheory.TorProducts.torBaseChange R A (n + m)).map
      (ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap) = _
  simp only [GradedTor.torPieceMap_ofNat]
  unfold GradedTor.torMultiplication
  let f := ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap
  let ff : (GradedTor.liftedModule R A B, GradedTor.liftedModule R A B) ⟶
      (GradedTor.liftedModule R A C, GradedTor.liftedModule R A C) := (f, f)
  have hmap :
      ((RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).prod
          (RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A m) ⋙
        RingTheory.TorProducts.tensorBifunctor.{uA, max uR v} A).map ff =
      TorCrossProduct.moduleTensorMap.{max uR uA v, uA}
        ((RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A n).map f)
        ((RingTheory.TorProducts.torBaseChange.{uR, uA, v} R A m).map f) := rfl
  have hmapR :
      (RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).map ff =
        TorCrossProduct.moduleTensorMap.{max uR uA v, uR} f f := rfl
  rw [← hmap, Category.assoc, ← Functor.map_comp, ← liftedMap_mul R A g, Functor.map_comp,
    ← hmapR, ← Functor.comp_map, ← Category.assoc,
    ← (RingTheory.TorProducts.torProduct R A n m).naturality ff, Category.assoc]

private lemma zeroBaseChange_mul_one (B : AlgCat.{max uR uA v, uR} R)
    (x : (extensionScalars.{uR, uA, v} (algebraMap R A)).obj
      (ModuleCat.of R B)) :
    ((TorCrossProduct.zeroBaseChange.{uR, uA, v} R A (algebraMap R A)
        (ModuleCat.of R B) (ModuleCat.of R B)) ≫
      (extensionScalars.{uR, uA, v} (algebraMap R A)).map
        (ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul R B))))
      (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R, algebraMap R A] (1 : B))) = x := by
  let f := algebraMap R A
  let := f.toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change (extensionScalars.{uR, uA, v} (algebraMap R A)).map
      (ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul R B)))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A B B).symm
        ((a ⊗ₜ[R] b) ⊗ₜ[A] ((1 : A) ⊗ₜ[R, algebraMap R A] (1 : B)))) = _
    simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, mul_one]
    change a ⊗ₜ[R] (b * 1) = a ⊗ₜ[R] b
    rw [mul_one]
  | add x y hx hy => simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy

private lemma torMultiplication_fromLeftDerivedZero (B : AlgCat.{v, uR} R) :
    GradedTor.torMultiplication R A B 0 0 ≫
        (extensionScalars.{uR, uA, v} (algebraMap R A)).fromLeftDerivedZero.app
          (GradedTor.liftedModule R A B) =
      TorCrossProduct.moduleTensorMap.{uR, uA, v}
          ((extensionScalars.{uR, uA, v}
            (algebraMap R A)).fromLeftDerivedZero.app
            (GradedTor.liftedModule R A B))
          ((extensionScalars.{uR, uA, v}
            (algebraMap R A)).fromLeftDerivedZero.app
            (GradedTor.liftedModule R A B)) ≫
        TorCrossProduct.zeroBaseChange.{uR, uA, v} R A (algebraMap R A)
          (GradedTor.liftedModule R A B) (GradedTor.liftedModule R A B) ≫
        (extensionScalars.{uR, uA, v} (algebraMap R A)).map
          (ModuleCat.ofHom (TensorProduct.lift
            (LinearMap.mul R (GradedTor.liftedAlgebra R A B)))) := by
  unfold GradedTor.torMultiplication
  rw [Category.assoc, NatTrans.naturality, ← Category.assoc,
    RingTheory.TorProducts.torProduct_degree_zero, Category.assoc]

private lemma fromLeftDerivedZero_one (B : AlgCat.{v, uR} R) :
    (extensionScalars.{uR, uA, v} (algebraMap R A)).fromLeftDerivedZero.app
        (GradedTor.liftedModule R A B) (GradedTor.canonicalAlgebra R A B).one =
      (1 : A) ⊗ₜ[R, algebraMap R A] (1 : GradedTor.liftedAlgebra R A B) := by
  let F := extensionScalars.{uR, uA, v} (algebraMap R A)
  have : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} (algebraMap R A)).isLeftAdjoint
  let M := GradedTor.liftedModule R A B
  let e := F.leftDerivedZeroIsoSelf.app M
  let z : F.obj M := (1 : A) ⊗ₜ[R, algebraMap R A] (1 : GradedTor.liftedAlgebra R A B)
  let y : GradedTor.torPiece R A B 0 := e.inv z
  have hy : F.fromLeftDerivedZero.app M y = z := ConcreteCategory.congr_hom e.inv_hom_id z
  have hunit := (GradedTor.canonicalAlgebra R A B).one_mul 0 y
  change (GradedTor.canonicalAlgebra R A B).mul 0 0
    ((GradedTor.canonicalAlgebra R A B).one ⊗ₜ[A] y) = y at hunit
  erw [GradedTor.canonical_mul_ofNat R A B 0 0] at hunit
  have h := congrArg (F.fromLeftDerivedZero.app M) hunit
  change (GradedTor.torMultiplication R A B 0 0 ≫
    F.fromLeftDerivedZero.app M) _ = _ at h
  rw [torMultiplication_fromLeftDerivedZero] at h
  change ((TorCrossProduct.zeroBaseChange.{uR, uA, v} R A (algebraMap R A) M M) ≫
      F.map (ModuleCat.ofHom (TensorProduct.lift
        (LinearMap.mul R (GradedTor.liftedAlgebra R A B)))))
    ((F.fromLeftDerivedZero.app M (GradedTor.canonicalAlgebra R A B).one) ⊗ₜ[A]
      F.fromLeftDerivedZero.app M y) = F.fromLeftDerivedZero.app M y at h
  rw [hy] at h
  exact (zeroBaseChange_mul_one R A (GradedTor.liftedAlgebra R A B) _).symm.trans h

private lemma torPieceMap_one {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    GradedTor.torPieceMap.{uR, uA, v} R A g 0
        (GradedTor.canonicalAlgebra.{uR, uA, v} R A B).one =
      (GradedTor.canonicalAlgebra.{uR, uA, v} R A C).one := by
  let F := extensionScalars.{uR, uA, v} (algebraMap R A)
  have : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} (algebraMap R A)).isLeftAdjoint
  apply (ModuleCat.mono_iff_injective
    (F.fromLeftDerivedZero.app (GradedTor.liftedModule R A C))).mp inferInstance
  change ((F.leftDerived 0).map
      (ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap) ≫
    F.fromLeftDerivedZero.app (GradedTor.liftedModule R A C)) _ = _
  rw [NatTrans.naturality]
  change F.map (ModuleCat.ofHom (GradedTor.liftedMap R A g).hom.toLinearMap)
    (F.fromLeftDerivedZero.app (GradedTor.liftedModule R A B)
      (GradedTor.canonicalAlgebra R A B).one) = _
  rw [fromLeftDerivedZero_one, fromLeftDerivedZero_one]
  change (1 : A) ⊗ₜ[R, algebraMap R A]
    ((GradedTor.liftedMap R A g).hom (1 : GradedTor.liftedAlgebra R A B)) = _
  rw [map_one]

/-- Any two elements of a negative-degree piece of graded Tor are equal. -/
private lemma torPiece_negSucc_ext {B : AlgCat.{v, uR} R} {n : ℕ}
    (x y : GradedTor.torPiece.{uR, uA, v} R A B (Int.negSucc n)) : x = y :=
  Subsingleton.elim (α := zeroModule.{uR, uA, v} R A) x y

/-- Any two maps between negative-degree pieces of graded Tor are equal. -/
private lemma torPiece_negSucc_hom_ext {B C : AlgCat.{v, uR} R} {n : ℕ}
    (f f' : GradedTor.torPiece.{uR, uA, v} R A B (Int.negSucc n) ⟶
      GradedTor.torPiece.{uR, uA, v} R A C (Int.negSucc n)) : f = f' :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => torPiece_negSucc_ext R A _ _)

private lemma torPieceMap_mul {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    ∀ (i j : ℤ) (x : GradedTor.torPiece.{uR, uA, v} R A B i)
        (y : GradedTor.torPiece.{uR, uA, v} R A B j),
      GradedTor.torPieceMap.{uR, uA, v} R A g (i + j)
          ((GradedTor.canonicalAlgebra.{uR, uA, v} R A B).mul i j (x ⊗ₜ[A] y)) =
        (GradedTor.canonicalAlgebra.{uR, uA, v} R A C).mul i j
          (GradedTor.torPieceMap.{uR, uA, v} R A g i x ⊗ₜ[A]
            GradedTor.torPieceMap.{uR, uA, v} R A g j y) := by
  intro i j x y
  cases i with
  | ofNat n =>
    cases j with
    | ofNat m =>
      simp only [Int.ofNat_eq_natCast]
      rw [GradedTor.canonical_mul_ofNat, GradedTor.canonical_mul_ofNat]
      change (GradedTor.torMultiplication R A B n m ≫
        GradedTor.torPieceMap R A g (n + m)) (x ⊗ₜ[A] y) = _
      rw [map_torMultiplication R A g n m]
      rfl
    | negSucc m =>
      rw [torPiece_negSucc_ext R A y 0]
      simp only [TensorProduct.tmul_zero, map_zero]
  | negSucc n =>
    rw [torPiece_negSucc_ext R A x 0]
    simp only [TensorProduct.zero_tmul, map_zero]

/-- The maps on Tor induced by an `R`-algebra homomorphism assemble into a
homomorphism of the canonical graded `A`-algebras on Tor: they preserve the unit and the
homogeneous multiplication. -/
@[stacks 068K, sga "6 VII 2.1" "partial"]
public theorem torPieceMap_isAlgebraHom {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    torPieceMap.{uR, uA, v} R A g 0 (canonicalAlgebra.{uR, uA, v} R A B).one =
      (canonicalAlgebra.{uR, uA, v} R A C).one ∧
    ∀ (i j : ℤ) (x : torPiece.{uR, uA, v} R A B i)
        (y : torPiece.{uR, uA, v} R A B j),
      torPieceMap.{uR, uA, v} R A g (i + j)
          ((canonicalAlgebra.{uR, uA, v} R A B).mul i j (x ⊗ₜ[A] y)) =
        (canonicalAlgebra.{uR, uA, v} R A C).mul i j
          (torPieceMap.{uR, uA, v} R A g i x ⊗ₜ[A]
            torPieceMap.{uR, uA, v} R A g j y) :=
  ⟨torPieceMap_one R A g, torPieceMap_mul R A g⟩

end GradedTor

end

@[expose] public noncomputable section

open CategoryTheory
open scoped MonoidalCategory

namespace GradedTor

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]

/-- The canonical graded algebra map on Tor induced by an `R`-algebra map. -/
@[sga "6 VII 2.1" "partial"]
public noncomputable def canonicalMap {B C : AlgCat.{v, uR} R} (g : B ⟶ C) :
    AlgebraHom.{uR, uA, v} R A
      (canonicalAlgebra.{uR, uA, v} R A B) (canonicalAlgebra.{uR, uA, v} R A C) :=
  { hom := torPieceMap.{uR, uA, v} R A g
    map_one := (torPieceMap_isAlgebraHom.{uR, uA, v} R A g).1
    map_mul := (torPieceMap_isAlgebraHom.{uR, uA, v} R A g).2 }

/-- The degree-`i` map of the canonical graded algebra map is the functorial map on Tor. -/
public lemma canonical_map_hom {B C : AlgCat.{v, uR} R} (g : B ⟶ C) (i : ℤ) :
    (canonicalMap.{uR, uA, v} R A g).hom i = torPieceMap.{uR, uA, v} R A g i :=
  rfl

/-- The identity algebra map induces the identity in each Tor degree. -/
@[simp]
public lemma torPieceMap_id (B : AlgCat.{v, uR} R) (i : ℤ) :
    torPieceMap.{uR, uA, v} R A (𝟙 B) i = 𝟙 _ := by
  cases i with
  | ofNat n =>
    change (RingTheory.TorProducts.torBaseChange R A n).map _ = _
    have h : ModuleCat.ofHom (liftedMap R A (𝟙 B)).hom.toLinearMap =
        𝟙 (liftedModule R A B) := by
      ext x
      rfl
    rw [h]
    exact (RingTheory.TorProducts.torBaseChange R A n).map_id _
  | negSucc n => exact torPiece_negSucc_hom_ext R A _ _

/-- The degreewise Tor maps respect composition of algebra maps. -/
public lemma torPieceMap_comp {B C D : AlgCat.{v, uR} R} (g : B ⟶ C) (h : C ⟶ D)
    (i : ℤ) :
    torPieceMap.{uR, uA, v} R A (g ≫ h) i =
      torPieceMap.{uR, uA, v} R A g i ≫ torPieceMap.{uR, uA, v} R A h i := by
  cases i with
  | ofNat n =>
    change (RingTheory.TorProducts.torBaseChange R A n).map _ =
      (RingTheory.TorProducts.torBaseChange R A n).map _ ≫
        (RingTheory.TorProducts.torBaseChange R A n).map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  | negSucc n => exact torPiece_negSucc_hom_ext R A _ _

/-- The identity algebra map induces the identity on graded Tor. -/
@[simp]
public lemma canonical_map_id (B : AlgCat.{v, uR} R) (i : ℤ) :
    (canonicalMap.{uR, uA, v} R A (𝟙 B)).hom i = 𝟙 _ := by
  rw [canonical_map_hom, torPieceMap_id]

/-- Graded Tor maps respect composition of algebra maps. -/
public lemma canonical_map_comp {B C D : AlgCat.{v, uR} R} (g : B ⟶ C) (h : C ⟶ D)
    (i : ℤ) :
    (canonicalMap.{uR, uA, v} R A (g ≫ h)).hom i =
      (canonicalMap.{uR, uA, v} R A g).hom i ≫ (canonicalMap.{uR, uA, v} R A h).hom i := by
  simp only [canonical_map_hom, torPieceMap_comp]

/-- A graded algebra homomorphism is determined by its homogeneous components. -/
@[ext]
public lemma AlgebraHom.ext {B C : AlgCat.{v, uR} R} {X : Algebra.{uR, uA, v} R A B}
    {Y : Algebra.{uR, uA, v} R A C} {f g : AlgebraHom R A X Y}
    (h : ∀ i, f.hom i = g.hom i) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- The canonical graded Tor algebras and their maps, functorial in the `R`-algebra. -/
public structure FunctorialAlgebra where
  /-- The canonical graded algebra attached to an `R`-algebra. -/
  obj (B : AlgCat.{v, uR} R) : Algebra.{uR, uA, v} R A B
  /-- The canonical graded algebra map induced by an `R`-algebra map. -/
  map {B C : AlgCat.{v, uR} R} (g : B ⟶ C) : AlgebraHom.{uR, uA, v} R A (obj B) (obj C)
  /-- Its underlying degreewise map is functoriality of Tor. -/
  map_hom {B C : AlgCat.{v, uR} R} (g : B ⟶ C) (i : ℤ) :
    (map g).hom i = torPieceMap.{uR, uA, v} R A g i
  /-- Identity algebra maps induce identity maps in every degree. -/
  map_id (B : AlgCat.{v, uR} R) (i : ℤ) : (map (𝟙 B)).hom i = 𝟙 _
  /-- The construction respects composition of algebra maps. -/
  map_comp {B C D : AlgCat.{v, uR} R} (g : B ⟶ C) (h : C ⟶ D) (i : ℤ) :
    (map (g ≫ h)).hom i = (map g).hom i ≫ (map h).hom i

/-- The canonical functorial graded Tor algebra, given by `GradedTor.canonicalAlgebra` and
`GradedTor.canonicalMap`. -/
public noncomputable def canonical : FunctorialAlgebra.{uR, uA, v} R A where
  obj := canonicalAlgebra R A
  map := canonicalMap R A
  map_hom := canonical_map_hom R A
  map_id := canonical_map_id R A
  map_comp := canonical_map_comp R A

/-- Every system with the prescribed products and maps is the canonical one. -/
public theorem canonical_unique (F : FunctorialAlgebra.{uR, uA, v} R A) :
    F = canonical.{uR, uA, v} R A := by
  rcases F with ⟨obj, map, map_hom, map_id, map_comp⟩
  have hobj : obj = canonicalAlgebra R A :=
    funext fun B => canonicalAlgebra_unique R A B (obj B)
  cases hobj
  have hmap : @map = @canonicalMap R A _ _ _ := by
    funext B C g
    apply AlgebraHom.ext
    intro i
    exact (map_hom g i).trans (canonical_map_hom R A g i).symm
  cases hmap
  rfl

/-- There is a unique functorial graded Tor algebra with the prescribed products and maps. -/
public theorem existsUnique_functorialAlgebra :
    ∃! _ : FunctorialAlgebra.{uR, uA, v} R A, True :=
  ⟨canonical R A, trivial, fun F _ => canonical_unique R A F⟩

end GradedTor

end
