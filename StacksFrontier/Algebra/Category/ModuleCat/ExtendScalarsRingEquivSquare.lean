module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Extension of scalars across a square of ring isomorphisms

Let `e : R ≃+* R'` and `k : S ≃+* S'` be isomorphisms of commutative rings and let `φ : R →+* S`
and `φ' : R' →+* S'` be ring maps with `k ∘ φ = φ' ∘ e`.  Then base change along `φ` and base
change along `φ'` are the same operation: for an `R'`-module `M`,

  `S ⊗_R (restrictScalars e) M  ≅  (restrictScalars k) (S' ⊗_{R'} M)`,

an isomorphism of `S`-modules carrying `1 ⊗ m` to `1 ⊗ m`.

## Main definitions

* `Stacks.ModuleCat.ofRestrictHom` and `Stacks.ModuleCat.toRestrictHom` translate between
  `S'`-linear maps `P ⟶ (restrictScalars k.symm) Q` and `S`-linear maps
  `(restrictScalars k) P ⟶ Q`; they have the same underlying function.
* `Stacks.ModuleCat.extendScalarsSquareIso` is the isomorphism above, and
  `Stacks.ModuleCat.extendScalarsSquareNatIso` is its natural form.
* `Stacks.ModuleCat.extendScalarsTargetIso` is the case `R = R'` with `e` the identity, stated
  without a restriction of scalars on the source: base change along `φ : R →+* S` is base change
  along `φ' : R →+* S'`, read along an isomorphism `k : S ≃+* S'` with `k ∘ φ = φ'`.

## Main results

* `Stacks.ModuleCat.extendScalarsSquareHom_one_tmul` and
  `Stacks.ModuleCat.extendScalarsSquareInv_one_tmul`: both directions of the isomorphism send
  `1 ⊗ m` to `1 ⊗ m`.
* `Stacks.ModuleCat.exists_extendScalarsTargetHom`: an `S`-linear bijection from a base change
  along `φ` to an `S`-module identified, additively and semilinearly along `k`, with the base
  change along `φ'`.
* `Stacks.ModuleCat.bijective_of_extendScalarsTargetOut`: an `S'`-linear map out of a module
  identified with a base change along `φ'` is bijective if it is computed on the elements `1 ⊗ a`
  by a bijection out of the base change along `φ`.
* `Stacks.ModuleCat.exists_categoricalPullback_of_ringEquivSquare`: given two squares of ring
  isomorphisms as above over a common lower right corner, an `R'₁`-module `N`, an `R'₂`-module `M`
  and an isomorphism `γ` of their base changes to `S'`, there is an object of
  `CategoryTheory.Limits.CategoricalPullback` of the two base changes along the maps of the
  left-hand spelling whose components are `N` and `M` and whose compatible pairs are the pairs
  `γ (1 ⊗ n) = 1 ⊗ m`.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.ModuleCat

variable {R R' S S' : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']

/-! ### Maps out of a restriction of scalars along a ring isomorphism -/

section Restrict

variable (k : S ≃+* S') {P : ModuleCat.{u} S'} {Q : ModuleCat.{u} S}

/-- An `S'`-linear map from `P` to `Q` read as an `S'`-module along `k.symm` is the same
underlying function as an `S`-linear map from `P` read as an `S`-module along `k` to `Q`. -/
def ofRestrictHom (G : P ⟶ (ModuleCat.restrictScalars (k.symm : S' →+* S)).obj Q) :
    (ModuleCat.restrictScalars (k : S →+* S')).obj P ⟶ Q :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars (k : S →+* S')).obj P)
    { toFun := fun p => G p
      map_add' := fun p q => map_add G.hom p q
      map_smul' := fun s p =>
        (map_smul G.hom (k s) p).trans
          (congrArg (fun t : S => t • (G p : Q)) (k.symm_apply_apply s)) }

/-- `Stacks.ModuleCat.ofRestrictHom` has the same underlying function as the map it translates. -/
lemma ofRestrictHom_apply
    (G : P ⟶ (ModuleCat.restrictScalars (k.symm : S' →+* S)).obj Q) (p : P) :
    ofRestrictHom k G p = G p := rfl

/-- The translation inverse to `Stacks.ModuleCat.ofRestrictHom`. -/
def toRestrictHom (H : (ModuleCat.restrictScalars (k : S →+* S')).obj P ⟶ Q) :
    P ⟶ (ModuleCat.restrictScalars (k.symm : S' →+* S)).obj Q :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (k.symm : S' →+* S)).obj Q)
    { toFun := fun p => H p
      map_add' := fun p q => map_add H.hom p q
      map_smul' := fun s' p => by
        obtain ⟨s, rfl⟩ : ∃ s : S, k s = s' := ⟨k.symm s', k.apply_symm_apply s'⟩
        exact (map_smul H.hom s
            (show (ModuleCat.restrictScalars (k : S →+* S')).obj P from p)).trans
          (congrArg (fun t : S => t • (H p : Q)) (k.symm_apply_apply s).symm) }

/-- `Stacks.ModuleCat.toRestrictHom` has the same underlying function as the map it translates. -/
lemma toRestrictHom_apply
    (H : (ModuleCat.restrictScalars (k : S →+* S')).obj P ⟶ Q) (p : P) :
    toRestrictHom k H p = H p := rfl

/-- Two `S`-linear maps out of a restriction of scalars along `k` agree as soon as their
translations along `Stacks.ModuleCat.toRestrictHom` agree. -/
theorem hom_ext_of_toRestrictHom
    {α β : (ModuleCat.restrictScalars (k : S →+* S')).obj P ⟶ Q}
    (h : toRestrictHom k α = toRestrictHom k β) : α = β :=
  ModuleCat.hom_ext (LinearMap.ext fun p =>
    congrArg (fun t : P ⟶ (ModuleCat.restrictScalars (k.symm : S' →+* S)).obj Q => t p) h)

end Restrict

/-- The adjunction hom-equivalence inverts `G` to the map sending `1 ⊗ m` to `G m`. -/
private theorem homEquiv_symm_apply_one_tmul (f : R →+* S) {M : ModuleCat.{u} R}
    {N : ModuleCat.{u} S} (G : M ⟶ (ModuleCat.restrictScalars f).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm G ((1 : S) ⊗ₜ[R,f] m) = G m :=
  (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply _ m).symm.trans
    (congrArg (fun t => t m) (Equiv.apply_symm_apply _ G))

/-! ### The comparison of the two base changes -/

section Square

variable (e : R ≃+* R') (k : S ≃+* S') (φ : R →+* S) (φ' : R' →+* S')
  (hsq : ∀ r : R, k (φ r) = φ' (e r))

/-- The `R`-linear map `m ↦ 1 ⊗ m` from `M` restricted along `e` into `S' ⊗_{R'} M` read as an
`S`-module along `k`. -/
def squareUnit (M : ModuleCat.{u} R') :
    (ModuleCat.restrictScalars (e : R →+* R')).obj M ⟶
      (ModuleCat.restrictScalars φ).obj
        ((ModuleCat.restrictScalars (k : S →+* S')).obj
          ((ModuleCat.extendScalars φ').obj M)) :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars (e : R →+* R')).obj M)
    (Y := (ModuleCat.restrictScalars φ).obj
      ((ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M)))
    { toFun := fun m => (1 : S') ⊗ₜ[R',φ'] m
      map_add' := fun m m' => TensorProduct.tmul_add _ _ _
      map_smul' := fun r m => by
        let instS' : Module R' S' := Module.compHom S' φ'
        have key : ∀ (q : R') (n : (ModuleCat.restrictScalars (e : R →+* R')).obj M),
            (1 : S') ⊗ₜ[R',φ'] (q • n) = (φ' q * 1) ⊗ₜ[R',φ'] n := fun q n => by
          rw [← TensorProduct.smul_tmul]
          rfl
        have h := key (e r) m
        rwa [← hsq] at h }

/-- The `R'`-linear map `m ↦ 1 ⊗ m` from `M` into `S ⊗_R M` read as an `R'`-module along `e` and
as an `S'`-module along `k.symm`. -/
def squareCounit (M : ModuleCat.{u} R') :
    M ⟶ (ModuleCat.restrictScalars φ').obj
      ((ModuleCat.restrictScalars (k.symm : S' →+* S)).obj
        ((ModuleCat.extendScalars φ).obj
          ((ModuleCat.restrictScalars (e : R →+* R')).obj M))) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ').obj
      ((ModuleCat.restrictScalars (k.symm : S' →+* S)).obj
        ((ModuleCat.extendScalars φ).obj
          ((ModuleCat.restrictScalars (e : R →+* R')).obj M))))
    { toFun := fun m =>
        (1 : S) ⊗ₜ[R,φ] (show (ModuleCat.restrictScalars (e : R →+* R')).obj M from m)
      map_add' := fun m m' => TensorProduct.tmul_add _ _ _
      map_smul' := fun r' m => by
        obtain ⟨r, rfl⟩ : ∃ r : R, e r = r' := ⟨e.symm r', e.apply_symm_apply r'⟩
        let instS : Module R S := Module.compHom S φ
        have key : ∀ (q : R) (n : (ModuleCat.restrictScalars (e : R →+* R')).obj M),
            (1 : S) ⊗ₜ[R,φ] (q • n) = (φ q * 1) ⊗ₜ[R,φ] n := fun q n => by
          rw [← TensorProduct.smul_tmul]
          rfl
        have hφ : φ r = k.symm (φ' (e r)) := by rw [← hsq, k.symm_apply_apply]
        have h := key r m
        rwa [hφ] at h }

/-- The `S`-linear map `S ⊗_R (restrictScalars e) M ⟶ (restrictScalars k) (S' ⊗_{R'} M)` with
`1 ⊗ m ↦ 1 ⊗ m`. -/
def extendScalarsSquareHom (M : ModuleCat.{u} R') :
    (ModuleCat.extendScalars φ).obj ((ModuleCat.restrictScalars (e : R →+* R')).obj M) ⟶
      (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm (squareUnit e k φ φ' hsq M)

/-- The `S`-linear map `(restrictScalars k) (S' ⊗_{R'} M) ⟶ S ⊗_R (restrictScalars e) M` with
`1 ⊗ m ↦ 1 ⊗ m`. -/
def extendScalarsSquareInv (M : ModuleCat.{u} R') :
    (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) ⟶
      (ModuleCat.extendScalars φ).obj ((ModuleCat.restrictScalars (e : R →+* R')).obj M) :=
  ofRestrictHom k
    (((ModuleCat.extendRestrictScalarsAdj φ').homEquiv _ _).symm (squareCounit e k φ φ' hsq M))

/-- `Stacks.ModuleCat.extendScalarsSquareHom` sends `1 ⊗ n` to `1 ⊗ n`. -/
lemma extendScalarsSquareHom_one_tmul (M : ModuleCat.{u} R')
    (n : (ModuleCat.restrictScalars (e : R →+* R')).obj M) :
    extendScalarsSquareHom e k φ φ' hsq M ((1 : S) ⊗ₜ[R,φ] n) = (1 : S') ⊗ₜ[R',φ'] n :=
  homEquiv_symm_apply_one_tmul φ _ n

/-- `Stacks.ModuleCat.extendScalarsSquareInv` sends `1 ⊗ n` to `1 ⊗ n`. -/
lemma extendScalarsSquareInv_one_tmul (M : ModuleCat.{u} R')
    (n : (ModuleCat.restrictScalars (e : R →+* R')).obj M) :
    extendScalarsSquareInv e k φ φ' hsq M ((1 : S') ⊗ₜ[R',φ'] n) = (1 : S) ⊗ₜ[R,φ] n :=
  homEquiv_symm_apply_one_tmul φ' _ n

/-- For ring isomorphisms `e : R ≃+* R'`
and `k : S ≃+* S'` and ring maps `φ : R →+* S`, `φ' : R' →+* S'` with `k ∘ φ = φ' ∘ e`, base
change along `φ` of an `R'`-module read along `e` is base change along `φ'`, read along `k`. -/
def extendScalarsSquareIso (M : ModuleCat.{u} R') :
    (ModuleCat.extendScalars φ).obj ((ModuleCat.restrictScalars (e : R →+* R')).obj M) ≅
      (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) where
  hom := extendScalarsSquareHom e k φ φ' hsq M
  inv := extendScalarsSquareInv e k φ φ' hsq M
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext fun m =>
    (congrArg (fun z => extendScalarsSquareInv e k φ φ' hsq M z)
        (extendScalarsSquareHom_one_tmul e k φ φ' hsq M m)).trans
      (extendScalarsSquareInv_one_tmul e k φ φ' hsq M m)
  inv_hom_id := hom_ext_of_toRestrictHom k (ModuleCat.ExtendScalars.hom_ext fun m =>
    (congrArg (fun z => extendScalarsSquareHom e k φ φ' hsq M z)
        (extendScalarsSquareInv_one_tmul e k φ φ' hsq M m)).trans
      (extendScalarsSquareHom_one_tmul e k φ φ' hsq M m))

/-- The natural form of `Stacks.ModuleCat.extendScalarsSquareIso`. -/
def extendScalarsSquareNatIso :
    ModuleCat.restrictScalars (e : R →+* R') ⋙ ModuleCat.extendScalars φ ≅
      ModuleCat.extendScalars φ' ⋙ ModuleCat.restrictScalars (k : S →+* S') :=
  NatIso.ofComponents (fun M => extendScalarsSquareIso e k φ φ' hsq M) fun {M N} u =>
    ModuleCat.ExtendScalars.hom_ext fun n =>
      (extendScalarsSquareHom_one_tmul e k φ φ' hsq N (u n)).trans
        (congrArg (fun z => (ModuleCat.extendScalars φ').map u z)
          (extendScalarsSquareHom_one_tmul e k φ φ' hsq M n)).symm

/-! ### Renaming the target ring only -/

section Target

variable (k : S ≃+* S') (φ : R →+* S) (φ' : R →+* S') (hsq : ∀ r : R, k (φ r) = φ' r)

/-- The `R`-linear map `m ↦ 1 ⊗ m` from `M` into `S' ⊗_R M` read as an `S`-module along `k`. -/
def targetUnit (M : ModuleCat.{u} R) :
    M ⟶ (ModuleCat.restrictScalars φ).obj
      ((ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj
      ((ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M)))
    { toFun := fun m => (1 : S') ⊗ₜ[R,φ'] m
      map_add' := fun m m' => TensorProduct.tmul_add _ _ _
      map_smul' := fun r m => by
        let instS' : Module R S' := Module.compHom S' φ'
        have key : ∀ (q : R) (n : M), (1 : S') ⊗ₜ[R,φ'] (q • n) = (φ' q * 1) ⊗ₜ[R,φ'] n :=
          fun q n => by
            rw [← TensorProduct.smul_tmul]
            rfl
        have h := key r m
        rwa [← hsq] at h }

/-- The `R`-linear map `m ↦ 1 ⊗ m` from `M` into `S ⊗_R M` read as an `S'`-module along
`k.symm`. -/
def targetCounit (M : ModuleCat.{u} R) :
    M ⟶ (ModuleCat.restrictScalars φ').obj
      ((ModuleCat.restrictScalars (k.symm : S' →+* S)).obj ((ModuleCat.extendScalars φ).obj M)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ').obj
      ((ModuleCat.restrictScalars (k.symm : S' →+* S)).obj ((ModuleCat.extendScalars φ).obj M)))
    { toFun := fun m => (1 : S) ⊗ₜ[R,φ] m
      map_add' := fun m m' => TensorProduct.tmul_add _ _ _
      map_smul' := fun r m => by
        let instS : Module R S := Module.compHom S φ
        have key : ∀ (q : R) (n : M), (1 : S) ⊗ₜ[R,φ] (q • n) = (φ q * 1) ⊗ₜ[R,φ] n :=
          fun q n => by
            rw [← TensorProduct.smul_tmul]
            rfl
        have hφ : φ r = k.symm (φ' r) := by rw [← hsq, k.symm_apply_apply]
        have h := key r m
        rwa [hφ] at h }

/-- The `S`-linear map `S ⊗_R M ⟶ (restrictScalars k) (S' ⊗_R M)` with `1 ⊗ m ↦ 1 ⊗ m`. -/
def extendScalarsTargetHom (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ).obj M ⟶
      (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm (targetUnit k φ φ' hsq M)

/-- The `S`-linear map `(restrictScalars k) (S' ⊗_R M) ⟶ S ⊗_R M` with `1 ⊗ m ↦ 1 ⊗ m`. -/
def extendScalarsTargetInv (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) ⟶
      (ModuleCat.extendScalars φ).obj M :=
  ofRestrictHom k
    (((ModuleCat.extendRestrictScalarsAdj φ').homEquiv _ _).symm (targetCounit k φ φ' hsq M))

/-- `Stacks.ModuleCat.extendScalarsTargetHom` sends `1 ⊗ m` to `1 ⊗ m`. -/
lemma extendScalarsTargetHom_one_tmul (M : ModuleCat.{u} R) (m : M) :
    extendScalarsTargetHom k φ φ' hsq M ((1 : S) ⊗ₜ[R,φ] m) = (1 : S') ⊗ₜ[R,φ'] m :=
  homEquiv_symm_apply_one_tmul φ _ m

/-- `Stacks.ModuleCat.extendScalarsTargetInv` sends `1 ⊗ m` to `1 ⊗ m`. -/
lemma extendScalarsTargetInv_one_tmul (M : ModuleCat.{u} R) (m : M) :
    extendScalarsTargetInv k φ φ' hsq M ((1 : S') ⊗ₜ[R,φ'] m) = (1 : S) ⊗ₜ[R,φ] m :=
  homEquiv_symm_apply_one_tmul φ' _ m

/-- Base change along `φ` is base change along `φ'`, read along `k`, for `k ∘ φ = φ'` with `k` an
isomorphism of the target ring.  Both directions send `1 ⊗ m` to `1 ⊗ m`. -/
def extendScalarsTargetIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ).obj M ≅
      (ModuleCat.restrictScalars (k : S →+* S')).obj ((ModuleCat.extendScalars φ').obj M) where
  hom := extendScalarsTargetHom k φ φ' hsq M
  inv := extendScalarsTargetInv k φ φ' hsq M
  hom_inv_id := ModuleCat.ExtendScalars.hom_ext fun m =>
    (congrArg (fun z => extendScalarsTargetInv k φ φ' hsq M z)
        (extendScalarsTargetHom_one_tmul k φ φ' hsq M m)).trans
      (extendScalarsTargetInv_one_tmul k φ φ' hsq M m)
  inv_hom_id := hom_ext_of_toRestrictHom k (ModuleCat.ExtendScalars.hom_ext fun m =>
    (congrArg (fun z => extendScalarsTargetHom k φ φ' hsq M z)
        (extendScalarsTargetInv_one_tmul k φ φ' hsq M m)).trans
      (extendScalarsTargetHom_one_tmul k φ φ' hsq M m))

/-- Let `k : S ≃+* S'` and `φ : R →+* S`, `φ' : R →+* S'` with `k ∘ φ = φ'`, let `aff` identify
the base change of `L` along `φ'` with an `S'`-module `Q`, and let `e` identify an `S`-module `P`
with `Q` additively and semilinearly along `k`.  Then there is an `S`-linear bijection from the
base change of `L` along `φ` to `P` sending `1 ⊗ a` to the element of `P` that `e` carries to
`aff (1 ⊗ a)`. -/
theorem exists_extendScalarsTargetHom
    (k : S ≃+* S') (φ : R →+* S) (φ' : R →+* S') (hsq : ∀ r : R, k (φ r) = φ' r)
    (L : ModuleCat.{u} R) (Q : ModuleCat.{u} S')
    (aff : (ModuleCat.extendScalars φ').obj L ≅ Q)
    (P : ModuleCat.{u} S) (e : P ≃ Q)
    (hadd : ∀ x y : P, e (x + y) = e x + e y)
    (hsmul : ∀ (z : S) (x : P), e (z • x) = k z • e x) :
    ∃ β : (ModuleCat.extendScalars φ).obj L ⟶ P, Function.Bijective β ∧
      ∀ a : L, e (β ((1 : S) ⊗ₜ[R,φ] a)) = aff.hom ((1 : S') ⊗ₜ[R,φ'] a) := by
  have hesymm_add : ∀ y y' : Q, e.symm (y + y') = e.symm y + e.symm y' := fun y y' =>
    e.injective (by rw [e.apply_symm_apply, hadd, e.apply_symm_apply, e.apply_symm_apply])
  have hesymm_smul : ∀ (z : S) (y : Q), e.symm (k z • y) = z • e.symm y := fun z y =>
    e.injective (by rw [e.apply_symm_apply, hsmul, e.apply_symm_apply])
  let eInv : (ModuleCat.restrictScalars (k : S →+* S')).obj Q ⟶ P :=
    ModuleCat.ofHom (X := (ModuleCat.restrictScalars (k : S →+* S')).obj Q) (Y := P)
      { toFun := e.symm
        map_add' := hesymm_add
        map_smul' := fun z y => hesymm_smul z y }
  have : IsIso eInv := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact e.symm.bijective
  refine ⟨extendScalarsTargetHom k φ φ' hsq L ≫
    (ModuleCat.restrictScalars (k : S →+* S')).map aff.hom ≫ eInv, ?_, fun a => ?_⟩
  · have : IsIso (extendScalarsTargetHom k φ φ' hsq L) :=
      (extendScalarsTargetIso k φ φ' hsq L).isIso_hom
    exact ConcreteCategory.bijective_of_isIso _
  · change e (e.symm (aff.hom (extendScalarsTargetHom k φ φ' hsq L ((1 : S) ⊗ₜ[R,φ] a)))) = _
    rw [e.apply_symm_apply, extendScalarsTargetHom_one_tmul]
    rfl

/-- Let `k : S ≃+* S'` and `φ : R →+* S`, `φ' : R →+* S'` with `k ∘ φ = φ'`, let `aff` identify
the base change of `L` along `φ'` with an `S'`-module `Q` and let `c : Q ⟶ Qt` be `S'`-linear.  If
some `S`-linear bijection `δ` out of the base change of `L` along `φ` computes `c` on the elements
`1 ⊗ a`, through an additive bijection `e` semilinear along `k`, then `c` is bijective. -/
theorem bijective_of_extendScalarsTargetOut
    (k : S ≃+* S') (φ : R →+* S) (φ' : R →+* S') (hsq : ∀ r : R, k (φ r) = φ' r)
    (L : ModuleCat.{u} R) (Q : ModuleCat.{u} S')
    (aff : (ModuleCat.extendScalars φ').obj L ≅ Q)
    (Qt : ModuleCat.{u} S') (c : Q ⟶ Qt)
    (P : ModuleCat.{u} S) (e : P ≃ Qt)
    (hadd : ∀ x y : P, e (x + y) = e x + e y)
    (hsmul : ∀ (z : S) (x : P), e (z • x) = k z • e x)
    (δ : (ModuleCat.extendScalars φ).obj L ⟶ P) (hδ : Function.Bijective δ)
    (hval : ∀ a : L, e (δ ((1 : S) ⊗ₜ[R,φ] a)) = c (aff.hom ((1 : S') ⊗ₜ[R,φ'] a))) :
    Function.Bijective c := by
  let eHom : P ⟶ (ModuleCat.restrictScalars (k : S →+* S')).obj Qt :=
    ModuleCat.ofHom (X := P) (Y := (ModuleCat.restrictScalars (k : S →+* S')).obj Qt)
      { toFun := e
        map_add' := hadd
        map_smul' := hsmul }
  have heHom : Function.Bijective eHom := e.bijective
  let β : (ModuleCat.extendScalars φ).obj L ⟶
      (ModuleCat.restrictScalars (k : S →+* S')).obj Q :=
    extendScalarsTargetHom k φ φ' hsq L ≫
      (ModuleCat.restrictScalars (k : S →+* S')).map aff.hom
  have hβ : Function.Bijective β := by
    have : IsIso (extendScalarsTargetHom k φ φ' hsq L) :=
      (extendScalarsTargetIso k φ φ' hsq L).isIso_hom
    have : IsIso ((ModuleCat.restrictScalars (k : S →+* S')).map aff.hom) :=
      have : IsIso aff.hom := aff.isIso_hom
      inferInstance
    exact ConcreteCategory.bijective_of_isIso β
  have hβval : ∀ a : L, β ((1 : S) ⊗ₜ[R,φ] a) = aff.hom ((1 : S') ⊗ₜ[R,φ'] a) := fun a =>
    congrArg (fun z => aff.hom z) (extendScalarsTargetHom_one_tmul k φ φ' hsq L a)
  have key : β ≫ (ModuleCat.restrictScalars (k : S →+* S')).map c = δ ≫ eHom :=
    ModuleCat.ExtendScalars.hom_ext fun a =>
      (congrArg (fun z => c z) (hβval a)).trans (hval a).symm
  have hcomp : Function.Bijective
      (fun x : (ModuleCat.extendScalars φ).obj L => c (β x)) := by
    have h1 : (fun x : (ModuleCat.extendScalars φ).obj L => c (β x)) =
        fun x => eHom (δ x) :=
      funext fun x => congrArg (fun t : (ModuleCat.extendScalars φ).obj L ⟶
        (ModuleCat.restrictScalars (k : S →+* S')).obj Qt =>
          ModuleCat.Hom.hom t x) key
    rw [h1]
    exact heHom.comp hδ
  refine ⟨fun x y hxy => ?_, fun w => ?_⟩
  · obtain ⟨a, ha⟩ := hβ.2 x
    obtain ⟨b, hb⟩ := hβ.2 y
    rw [← ha, ← hb] at hxy ⊢
    exact congrArg (fun t => β t) (hcomp.1 hxy)
  · obtain ⟨a, ha⟩ := hcomp.2 w
    exact ⟨β a, ha⟩

end Target

/-! ### An object of the categorical pullback of two base changes -/

/-- Let `kD : D ≃+* D₁`, `kA : A ≃+* A₁` and `kC : C ≃+* C₁` be ring isomorphisms and
let `DtoC : D →+* C`, `AtoC : A →+* C`, `ψD : D₁ →+* C₁`, `ψA : A₁ →+* C₁` be ring maps with
`kC ∘ DtoC = ψD ∘ kD` and `kC ∘ AtoC = ψA ∘ kA`.  An isomorphism `γ` between the base change of a
`D₁`-module `N` along `ψD` and the base change of an `A₁`-module `M` along `ψA` then gives an
object of the categorical pullback of the base changes along `DtoC` and `AtoC`, whose components
are `N` and `M` and whose compatible pairs — the pairs with `1 ⊗ n = 1 ⊗ m` in the structural
isomorphism — are exactly the pairs with `γ (1 ⊗ n) = 1 ⊗ m`.

The two component identifications are additive and semilinear along `kD` and `kA`. -/
theorem exists_categoricalPullback_of_ringEquivSquare
    {D A C D₁ A₁ C₁ : Type u} [CommRing D] [CommRing A] [CommRing C]
    [CommRing D₁] [CommRing A₁] [CommRing C₁]
    (kD : D ≃+* D₁) (kA : A ≃+* A₁) (kC : C ≃+* C₁)
    (DtoC : D →+* C) (AtoC : A →+* C) (ψD : D₁ →+* C₁) (ψA : A₁ →+* C₁)
    (hD : ∀ z : D, kC (DtoC z) = ψD (kD z)) (hA : ∀ z : A, kC (AtoC z) = ψA (kA z))
    (N : ModuleCat.{u} D₁) (M : ModuleCat.{u} A₁)
    (γ : (ModuleCat.extendScalars ψD).obj N ≅ (ModuleCat.extendScalars ψA).obj M) :
    ∃ (Xc : CategoryTheory.Limits.CategoricalPullback
        (ModuleCat.extendScalars.{u, u, u} DtoC) (ModuleCat.extendScalars.{u, u, u} AtoC))
      (eD : Xc.fst ≃ N) (eA : Xc.snd ≃ M),
      (∀ n n' : Xc.fst, eD (n + n') = eD n + eD n') ∧
        (∀ (z : D) (n : Xc.fst), eD (z • n) = kD z • eD n) ∧
        (∀ m m' : Xc.snd, eA (m + m') = eA m + eA m') ∧
        (∀ (z : A) (m : Xc.snd), eA (z • m) = kA z • eA m) ∧
        ∀ (n : Xc.fst) (m : Xc.snd),
          (Xc.iso.hom ((1 : C) ⊗ₜ[D,DtoC] n) = (1 : C) ⊗ₜ[A,AtoC] m) ↔
            γ.hom ((1 : C₁) ⊗ₜ[D₁,ψD] (eD n)) = (1 : C₁) ⊗ₜ[A₁,ψA] (eA m) := by
  let isoD := extendScalarsSquareIso kD kC DtoC ψD hD N
  let isoA := extendScalarsSquareIso kA kC AtoC ψA hA M
  have hisoD : ∀ n, isoD.hom ((1 : C) ⊗ₜ[D,DtoC] n) = (1 : C₁) ⊗ₜ[D₁,ψD] n :=
    extendScalarsSquareHom_one_tmul kD kC DtoC ψD hD N
  have hisoA : ∀ m, isoA.hom ((1 : C) ⊗ₜ[A,AtoC] m) = (1 : C₁) ⊗ₜ[A₁,ψA] m :=
    extendScalarsSquareHom_one_tmul kA kC AtoC ψA hA M
  have hAhi : ∀ x, isoA.hom (isoA.inv x) = x := fun x =>
    DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp isoA.inv_hom_id) x
  have hAih : ∀ x, isoA.inv (isoA.hom x) = x := fun x =>
    DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp isoA.hom_inv_id) x
  refine ⟨⟨_, _, isoD ≪≫ (ModuleCat.restrictScalars (kC : C →+* C₁)).mapIso γ ≪≫ isoA.symm⟩,
    Equiv.refl _, Equiv.refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun n m => ?_⟩
  have hXc : (isoD ≪≫ (ModuleCat.restrictScalars (kC : C →+* C₁)).mapIso γ ≪≫ isoA.symm).hom
      ((1 : C) ⊗ₜ[D,DtoC] n) = isoA.inv (γ.hom ((1 : C₁) ⊗ₜ[D₁,ψD] n)) :=
    congrArg (fun z => isoA.inv (γ.hom z)) (hisoD n)
  rw [hXc]
  exact ⟨fun h => (((hAhi _).symm.trans
      (congrArg (fun z => isoA.hom z) h)).trans (hisoA m)),
    fun h => (congrArg (fun z => isoA.inv z) h).trans
      (((congrArg (fun z => isoA.inv z) (hisoA m)).symm).trans (hAih _))⟩

end Square

end Stacks.ModuleCat

end
