module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrilinearPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality
public import StacksCore.Tactic.StacksAttribute

/-! # The double tensor product sheaf represents trilinear pairings

Let `(C, J)` be a site, let `A` be a presheaf of commutative rings on it whose underlying
presheaf of rings is a sheaf, and let `F`, `G`, `H`, `N` be sheaves of `A`-modules. Stacks 18.26
records that the tensor product sheaf represents bilinear pairings,
`Hom_A(F ⊗_A G, N) = Bilin_A(F × G, N)`; that is
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality`.

This file proves the **three-variable form**,
`Stacks.SheafOfModules.trilinearEquivTensorSheafHom`:

`Trilin_A(F × G × H, N) ≃ ((F ⊗_A G) ⊗_A H ⟶ N)`,

for a sheaf of rings on an arbitrary site and three arbitrary sheaves of modules over it — not
for the pullback. It is the form in which the associativity coherence
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence.associativity` of Tag 03EL turns
an identity of morphisms out of `(F ⊗ G) ⊗ H` into an identity of triple pairings, which is what
the transport of Tag 03D7 moves across `f⁻¹ ⊣ f_*`.

The binary proof factors through the objectwise tensor product and the sheafification
adjunction. The three-variable one cannot be a transcription of it, because in `(F ⊗_A G) ⊗_A H`
the left factor of the outer objectwise tensor product is **already a sheafification**, so the
sheafification comparison has to be composed with itself: once as
`Stacks.SheafOfModules.sheafifyDoubleTensorIso`, which identifies the sheafification of the
double objectwise tensor product `(F ⊗ G) ⊗ H` with the double tensor product sheaf, and once as
the sheafification adjunction. The first of those two is where the content sits, and it is
exactly Tag 05NA: sheafification inverts its own units
(`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify`) and the class of
morphisms it inverts is stable under tensoring
(`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight`), so the
sheafified unit of `F ⊗ G` whiskered by `H` is an isomorphism. In particular the outer pure
tensors are only *locally* inner pure tensors, and no statement here mentions them.

## Main definitions

* `CategoryTheory.Sheaf.ternaryOpHom`: a natural pointwise ternary operation on sections, as a
  morphism out of an iterated product of three sheaves of types. The three-variable form of
  `CategoryTheory.Sheaf.binaryOpHom`.
* `Stacks.SheafOfModules.triLift`: a trilinear function `M × N × P → Q` of modules over a
  commutative ring, as a linear map out of `(M ⊗ N) ⊗ P`.
* `Stacks.SheafOfModules.pairingOfTensorHom₃` and `Stacks.SheafOfModules.tensorHomOfPairing₃`:
  the passage between a triple pairing and a morphism out of the double objectwise tensor
  product, in both directions.
* `Stacks.SheafOfModules.sheafifyDoubleTensorIso`: the comparison identifying the sheafification
  of `(F ⊗ G) ⊗ H` with `(F ⊗_A G) ⊗_A H`.

## Main results

* `Stacks.SheafOfModules.trilinearEquivPresheafTensorHom`: the universal property of the double
  objectwise tensor product. The three-variable form of
  `Stacks.SheafOfModules.bilinearEquivPresheafTensorHom`.
* `Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom`: morphisms of sheaves of
  modules out of `(F ⊗_A G) ⊗_A H` are morphisms of presheaves of modules out of `(F ⊗ G) ⊗ H`.
  The three-variable form of
  `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom`, and the step which is not a
  transcription.
* `Stacks.SheafOfModules.trilinearEquivTensorSheafHom`: **the double tensor product sheaf
  represents trilinear pairings.**
* `Stacks.SheafOfModules.isTrilinearPairing_pairingOfTensorHom₃`: the triple pairing determined
  by a morphism out of the double objectwise tensor product is trilinear.

## Implementation notes

`CategoryTheory.Sheaf.ternaryOpHom` is built from `CategoryTheory.Sheaf.binaryOpHom` by reading
a ternary operation as a binary one on `A ⨯ B` and `D`; written out directly, its naturality
proof has to rewrite the naturality of a *composite* projection, and the rewrite then has to be
iterated an awkward number of times.

`Stacks.SheafOfModules.triLift` goes through `Stacks.SheafOfModules.triLiftAux`, a linear map
`M ⊗ N →ₗ P →ₗ Q`, rather than lifting the three variables at once: the target of a
`TensorProduct.lift` has to be a module, and `P →ₗ[R] Q` is one because `R` is commutative. The
four linearity conditions the outer lift then asks for are the additivity and homogeneity of
that linear map and of its values, so none of them has to be proved by induction on a tensor.

The section proving the sheaf-level statements activates
`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules` as a local instance. The objectwise
tensor product of two presheaves of modules indexed by
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA` — which is where the codomain
of a sheafification unit lives — is not found by instance search otherwise: that index is a
plain definition, so Mathlib's monoidal structure, which is keyed on a composite with
`forget₂ CommRingCat RingCat`, does not match it syntactically. It is the same structure, and
the two spellings meet where `isIso_sheafify_map_whiskerRight` is applied.

The third module of the presheaf-level section is called `D` rather than `C`, which names the
site.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u

namespace CategoryTheory.Sheaf

open _root_.CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section TernaryOperations

variable {A B D E : Sheaf J (Type w)}

/-- A natural pointwise ternary operation on sections gives a morphism out of the iterated
product of three sheaves of types. This is the three-variable form of
`CategoryTheory.Sheaf.binaryOpHom`, and is built from it by reading the ternary operation as a
binary one on `A ⨯ B` and `D`. -/
noncomputable def ternaryOpHom
    (op : ∀ X : Cᵒᵖ, A.obj.obj X → B.obj.obj X → D.obj.obj X → E.obj.obj X)
    (hop : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (a : A.obj.obj X) (b : B.obj.obj X) (d : D.obj.obj X),
      E.obj.map g (op X a b d) =
        op Y (A.obj.map g a) (B.obj.map g b) (D.obj.map g d)) :
    (A ⨯ B) ⨯ D ⟶ E :=
  binaryOpHom (A := A ⨯ B) (B := D) (E := E)
    (fun X s d ↦ op X ((Limits.prod.fst : A ⨯ B ⟶ A).hom.app X s)
      ((Limits.prod.snd : A ⨯ B ⟶ B).hom.app X s) d)
    (fun {_ _} g s d ↦ by
      rw [hop g, NatTrans.naturality_apply, NatTrans.naturality_apply])

/-- On sections over `X`, the morphism `ternaryOpHom op hop` sends `((a, b), d)` to
`op X a b d`. -/
@[simp]
lemma sectionsFunctor_map_ternaryOpHom (op) (hop) (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj A) (b : (sectionsFunctor J X).obj B)
    (d : (sectionsFunctor J X).obj D) :
    (sectionsFunctor J X).map (ternaryOpHom (A := A) (B := B) (D := D) (E := E) op hop)
      (prodObjMk (prodObjMk a b) d) = op X a b d := by
  have h₁ : (Limits.prod.fst : A ⨯ B ⟶ A).hom.app X (prodObjMk a b) = a :=
    map_fst_prodObjMk (P := sectionsFunctor J X) a b
  have h₂ : (Limits.prod.snd : A ⨯ B ⟶ B).hom.app X (prodObjMk a b) = b :=
    map_snd_prodObjMk (P := sectionsFunctor J X) a b
  rw [ternaryOpHom, sectionsFunctor_map_binaryOpHom, h₁, h₂]

end TernaryOperations

end CategoryTheory.Sheaf

namespace Stacks.SheafOfModules

/-! ## Linear maps out of a double tensor product -/

section Aux

open scoped TensorProduct

variable {R : Type w} [CommRing R] {M N P Q : Type w} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- A linear map out of `(M ⊗ N) ⊗ P` is additive in the first factor. -/
private lemma map_add_tmul_tmul (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (m m' : M) (n : N) (p : P) :
    g (((m + m') ⊗ₜ[R] n) ⊗ₜ[R] p) = g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) + g ((m' ⊗ₜ[R] n) ⊗ₜ[R] p) := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add]

/-- A linear map out of `(M ⊗ N) ⊗ P` is additive in the second factor. -/
private lemma map_tmul_add_tmul (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (m : M) (n n' : N) (p : P) :
    g ((m ⊗ₜ[R] (n + n')) ⊗ₜ[R] p) = g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) + g ((m ⊗ₜ[R] n') ⊗ₜ[R] p) := by
  rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]

/-- A linear map out of `(M ⊗ N) ⊗ P` is additive in the third factor. -/
private lemma map_tmul_tmul_add (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (m : M) (n : N) (p p' : P) :
    g ((m ⊗ₜ[R] n) ⊗ₜ[R] (p + p')) = g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) + g ((m ⊗ₜ[R] n) ⊗ₜ[R] p') := by
  rw [TensorProduct.tmul_add, map_add]

/-- A linear map out of `(M ⊗ N) ⊗ P` carries a scalar out of the first factor. -/
private lemma map_smul_tmul_tmul (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (r : R) (m : M) (n : N)
    (p : P) : g (((r • m) ⊗ₜ[R] n) ⊗ₜ[R] p) = r • g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', map_smul]

/-- A linear map out of `(M ⊗ N) ⊗ P` carries a scalar out of the second factor. -/
private lemma map_tmul_smul_tmul (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (r : R) (m : M) (n : N)
    (p : P) : g ((m ⊗ₜ[R] (r • n)) ⊗ₜ[R] p) = r • g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) := by
  rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul]

/-- A linear map out of `(M ⊗ N) ⊗ P` carries a scalar out of the third factor. -/
private lemma map_tmul_tmul_smul (g : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q) (r : R) (m : M) (n : N)
    (p : P) : g ((m ⊗ₜ[R] n) ⊗ₜ[R] (r • p)) = r • g ((m ⊗ₜ[R] n) ⊗ₜ[R] p) := by
  rw [TensorProduct.tmul_smul, map_smul]

variable (f : M → N → P → Q)
  (ha₁ : ∀ (m m' : M) (n : N) (p : P), f (m + m') n p = f m n p + f m' n p)
  (hs₁ : ∀ (r : R) (m : M) (n : N) (p : P), f (r • m) n p = r • f m n p)
  (ha₂ : ∀ (m : M) (n n' : N) (p : P), f m (n + n') p = f m n p + f m n' p)
  (hs₂ : ∀ (r : R) (m : M) (n : N) (p : P), f m (r • n) p = r • f m n p)
  (ha₃ : ∀ (m : M) (n : N) (p p' : P), f m n (p + p') = f m n p + f m n p')
  (hs₃ : ∀ (r : R) (m : M) (n : N) (p : P), f m n (r • p) = r • f m n p)

/-- A trilinear function `M × N × P → Q`, read as a linear map `M ⊗ N →ₗ (P →ₗ Q)`. This is the
intermediate stage of `Stacks.SheafOfModules.triLift`: the target of a `TensorProduct.lift` has
to be a module, and `P →ₗ[R] Q` is one because `R` is commutative. -/
def triLiftAux : (M ⊗[R] N) →ₗ[R] P →ₗ[R] Q :=
  TensorProduct.lift (LinearMap.mk₂ R
    (fun (m : M) (n : N) ↦
      ({ toFun := f m n, map_add' := ha₃ m n, map_smul' := fun r p ↦ hs₃ r m n p } :
        P →ₗ[R] Q))
    (fun m m' n ↦ LinearMap.ext fun p ↦ ha₁ m m' n p)
    (fun r m n ↦ LinearMap.ext fun p ↦ hs₁ r m n p)
    (fun m n n' ↦ LinearMap.ext fun p ↦ ha₂ m n n' p)
    (fun r m n ↦ LinearMap.ext fun p ↦ hs₂ r m n p))

/-- **A trilinear function lifts to a linear map out of `(M ⊗ N) ⊗ P`.** -/
def triLift : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q :=
  TensorProduct.lift (triLiftAux f ha₁ hs₁ ha₂ hs₂ ha₃ hs₃)

/-- The linear map `triLift f ...` sends `(m ⊗ n) ⊗ p` to `f m n p`. -/
@[simp]
lemma triLift_tmul_tmul (m : M) (n : N) (p : P) :
    triLift f ha₁ hs₁ ha₂ hs₂ ha₃ hs₃ ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = f m n p := rfl

end Aux

/-! ## Trilinear pairings and the double objectwise tensor product -/

section PresheafTensor

open scoped TensorProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A B D N : SheafOfModules.{w} (commRingSheaf J O hO)}

/-- The triple pairing of local sections determined by a morphism out of the double objectwise
tensor product of the underlying presheaves of modules: pair three sections and take their
iterated tensor. -/
def pairingOfTensorHom₃ (t : (A.val ⊗ B.val) ⊗ D.val ⟶ N.val) :
    (moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B) ⨯
        moduleSheaf (commRingSheaf J O hO) D ⟶
      moduleSheaf (commRingSheaf J O hO) N :=
  ternaryOpHom (fun U (a : A.val.obj U) (b : B.val.obj U) (c : D.val.obj U) ↦
      t.app U ((a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c))
    (fun {U _} g a b c ↦ (PresheafOfModules.naturality_apply t g
      ((a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c)).symm)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The triple pairing determined by `t` sends local sections `a`, `b`, `c` over `U` to the value
of `t` at `(a ⊗ b) ⊗ c`. -/
@[simp]
lemma pairingApp₃_pairingOfTensorHom₃ (t : (A.val ⊗ B.val) ⊗ D.val ⟶ N.val) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (c : D.val.obj U) :
    pairingApp₃ (commRingSheaf J O hO) (pairingOfTensorHom₃ t) U a b c =
      t.app U ((a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c) :=
  sectionsFunctor_map_ternaryOpHom
    (A := moduleSheaf (commRingSheaf J O hO) A)
    (B := moduleSheaf (commRingSheaf J O hO) B)
    (D := moduleSheaf (commRingSheaf J O hO) D)
    (E := moduleSheaf (commRingSheaf J O hO) N) _ _ U a b c

/-- The triple pairing determined by a morphism out of the double objectwise tensor product is
trilinear. -/
lemma isTrilinearPairing_pairingOfTensorHom₃ (t : (A.val ⊗ B.val) ⊗ D.val ⟶ N.val) :
    IsTrilinearPairing (commRingSheaf J O hO) (pairingOfTensorHom₃ t) where
  add_left U a a' b c := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃,
      pairingApp₃_pairingOfTensorHom₃]
    exact map_add_tmul_tmul (t.app U).hom a a' b c
  add_mid U a b b' c := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃,
      pairingApp₃_pairingOfTensorHom₃]
    exact map_tmul_add_tmul (t.app U).hom a b b' c
  add_right U a b c c' := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃,
      pairingApp₃_pairingOfTensorHom₃]
    exact map_tmul_tmul_add (t.app U).hom a b c c'
  smul_left U r a b c := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃]
    exact map_smul_tmul_tmul (t.app U).hom r a b c
  smul_mid U r a b c := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃]
    exact map_tmul_smul_tmul (t.app U).hom r a b c
  smul_right U r a b c := by
    erw [pairingApp₃_pairingOfTensorHom₃, pairingApp₃_pairingOfTensorHom₃]
    exact map_tmul_tmul_smul (t.app U).hom r a b c

/-- The morphism out of the double objectwise tensor product of the underlying presheaves of
modules determined by a trilinear pairing of local sections. -/
def tensorHomOfPairing₃
    {p : (moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B) ⨯
      moduleSheaf (commRingSheaf J O hO) D ⟶ moduleSheaf (commRingSheaf J O hO) N}
    (hp : IsTrilinearPairing (commRingSheaf J O hO) p) :
    (A.val ⊗ B.val) ⊗ D.val ⟶ N.val where
  app U := ModuleCat.ofHom
    (triLift (fun (a : A.val.obj U) (b : B.val.obj U) (c : D.val.obj U) ↦
        pairingApp₃ (commRingSheaf J O hO) p U a b c)
      (hp.add_left U) (hp.smul_left U) (hp.add_mid U) (hp.smul_mid U) (hp.add_right U)
      (hp.smul_right U))
  naturality {U _} g := by
    refine ModuleCat.MonoidalCategory.tensor_ext₃' fun a b c ↦ ?_
    exact (pairingApp₃_naturality (commRingSheaf J O hO) p g a b c).symm

/-- The morphism determined by a trilinear pairing `p` sends `(a ⊗ b) ⊗ c` over `U` to the value
of `p` at the local sections `a`, `b`, `c`. -/
@[simp]
lemma tensorHomOfPairing₃_app_tmul_tmul
    {p : (moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B) ⨯
      moduleSheaf (commRingSheaf J O hO) D ⟶ moduleSheaf (commRingSheaf J O hO) N}
    (hp : IsTrilinearPairing (commRingSheaf J O hO) p) (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (c : D.val.obj U) :
    (tensorHomOfPairing₃ hp).app U
        ((a ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj U] b) ⊗ₜ c) =
      pairingApp₃ (commRingSheaf J O hO) p U a b c := rfl

/-- **The universal property of the double objectwise tensor product**: trilinear pairings of
the underlying sheaves of sets of `A`, `B` and `D` with values in `N` are the same thing as
morphisms of presheaves of modules out of `(A ⊗ B) ⊗ D`. -/
def trilinearEquivPresheafTensorHom :
    { p : (moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B) ⨯
        moduleSheaf (commRingSheaf J O hO) D ⟶ moduleSheaf (commRingSheaf J O hO) N //
      IsTrilinearPairing (commRingSheaf J O hO) p } ≃ ((A.val ⊗ B.val) ⊗ D.val ⟶ N.val) where
  toFun p := tensorHomOfPairing₃ p.2
  invFun t := ⟨pairingOfTensorHom₃ t, isTrilinearPairing_pairingOfTensorHom₃ t⟩
  left_inv p := Subtype.ext (pairing₃_ext _ fun U a b c ↦
    pairingApp₃_pairingOfTensorHom₃ (tensorHomOfPairing₃ p.2) U a b c)
  right_inv t := PresheafOfModules.hom_ext fun U ↦
    ModuleCat.MonoidalCategory.tensor_ext₃' fun a b c ↦
      pairingApp₃_pairingOfTensorHom₃ t U a b c

end PresheafTensor

/-! ## Trilinear pairings and the double tensor product sheaf -/

section TensorSheaf

attribute [local instance] monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} {hA : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A)}
  {F G H N : SheafOfModules.{w} (commRingSheaf J A hA)}

/-- The comparison identifying the sheafification of the double objectwise tensor product
`(F ⊗ G) ⊗ H` with the double tensor product sheaf `(F ⊗_A G) ⊗_A H`. It is the sheafification
of the sheafification unit of `F ⊗ G` whiskered by `H`, and it is an isomorphism because
sheafification inverts its own units and the class it inverts is stable under tensoring
(Tag 05NA). -/
def sheafifyDoubleTensorIso :
    (TensorSheafification.sheafify A hA).obj ((F.val ⊗ G.val) ⊗ H.val) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
            (F)).obj (G))))).obj (H)) :=
  @asIso _ _ _ _ ((TensorSheafification.sheafify A hA).map
      (TensorSheafification.toSheafify A hA (F.val ⊗ G.val) ▷ H.val))
    (TensorSheafification.isIso_sheafify_map_whiskerRight A hA
      (TensorSheafification.toSheafify A hA (F.val ⊗ G.val)) H.val
      (TensorSheafification.isIso_sheafify_map_toSheafify A hA (F.val ⊗ G.val)))

/-- Morphisms of sheaves of modules out of the double tensor product sheaf `(F ⊗_A G) ⊗_A H`
are the same thing as morphisms of presheaves of modules out of the double objectwise tensor
product `(F ⊗ G) ⊗ H`. This is the step of the three-variable universal property which is not a
transcription of the binary one: the left factor of the outer objectwise tensor product is
already a sheafification, so the sheafification comparison has to be composed with itself —
once as `Stacks.SheafOfModules.sheafifyDoubleTensorIso`, and once as the sheafification
adjunction. -/
def doubleTensorSheafHomEquivPresheafTensorHom :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
      (((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
          (F)).obj (G))))).obj (H)) ⟶ N) ≃
      ((F.val ⊗ G.val) ⊗ H.val ⟶ N.val) :=
  ((sheafifyDoubleTensorIso (F := F) (G := G) (H := H)).symm.homCongr (Iso.refl N)).trans
    ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A hA) (𝟙 _)).homEquiv
      ((F.val ⊗ G.val) ⊗ H.val) N)

/-- **The double tensor product sheaf represents trilinear pairings.** Trilinear pairings of the
underlying sheaves of sets of `F`, `G` and `H` with values in `N` are the same thing as
morphisms of sheaves of modules out of `(F ⊗_A G) ⊗_A H`. This is the three-variable form of
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom`, stated for a sheaf of rings on an arbitrary
site and three arbitrary sheaves of modules over it. -/
def trilinearEquivTensorSheafHom :
    { p : (moduleSheaf (commRingSheaf J A hA) F ⨯ moduleSheaf (commRingSheaf J A hA) G) ⨯
        moduleSheaf (commRingSheaf J A hA) H ⟶ moduleSheaf (commRingSheaf J A hA) N //
      IsTrilinearPairing (commRingSheaf J A hA) p } ≃
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ (A) (forget₂ CommRingCat RingCat) (hA)⟩).obj
              (F)).obj (G))))).obj (H)) ⟶ N) :=
  (trilinearEquivPresheafTensorHom (hO := hA)).trans
    (doubleTensorSheafHomEquivPresheafTensorHom (F := F) (G := G) (H := H) (N := N)).symm

end TensorSheaf

end Stacks.SheafOfModules

end
