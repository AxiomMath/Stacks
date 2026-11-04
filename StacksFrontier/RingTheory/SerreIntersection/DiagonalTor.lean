module

public import StacksFrontier.RingTheory.Tor.LongExactSequence
public import StacksFrontier.RingTheory.SerreIntersection.ComplementaryPowerSeries
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Reduction to the diagonal for `Tor` over two complementary ring maps

Let `α, β : R →+* B` be ring maps with a common retraction `π : B →+* R`. For `R`-modules `M` and
`N`, the `B`-module `(B ⊗_{R, α} M) ⊗_{R, β} N` tensored over `B` with `B ⧸ ker π` is `M ⊗_R N`.
When `R` is Noetherian, `B` is flat over `R` through `α` and `B ⊗_{R, α} M` is flat over `R`
through `β`, this extends to an isomorphism
`Tor_i^B((B ⊗_{R, α} M) ⊗_{R, β} N, B ⧸ ker π) ≅ Tor_i^R(N, M)` for finite `M` and `N`, and the
two `Tor` modules have the same length.

## Main definitions

* `Twist`: a `B`-module regarded as an `R`-module through a ring map `R →+* B`.
* `Pair`: the `B`-module `(B ⊗_{R, α} M) ⊗_{R, β} N`.
* `Diag`: the quotient `B ⧸ ker π`.
* `diagEquiv`: the isomorphism `((B ⊗_{R, α} M) ⊗_{R, β} N) ⊗_B (B ⧸ ker π) ≅ M ⊗_R N`.

## Main results

* `isZero_tor'_pair_pi`: `Tor_{k+1}^B((B ⊗_{R, α} M) ⊗_{R, β} R^m, B ⧸ ker π) = 0`.
* `nonempty_tor'_pair_equiv`: the isomorphism of `Tor` modules in positive degrees.
* `length_tor_diag_pair`: the equality of lengths of `Tor` modules in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.SerreIntersection

section Shift

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)}

/-- The connecting morphism of the long exact sequence of `Tor_•(-, Q)` is an isomorphism as soon
as both middle terms flanking it vanish. -/
theorem isIso_Tor'δFirst (hS : S.ShortExact) (Q : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj Q))
    (h' : IsZero (((Tor' (ModuleCat.{u} R) n).obj S.X₂).obj Q)) :
    IsIso (Stacks.Tor.Tor'δFirst hS Q n) := by
  have hex := Stacks.Tor.Tor'_composableArrows_exact_first hS Q n
  have hmono : Mono (Stacks.Tor.Tor'δFirst hS Q n) := (hex.exact' 1 2 3).mono_g (h.eq_of_src _ _)
  have hepi : Epi (Stacks.Tor.Tor'δFirst hS Q n) := (hex.exact' 2 3 4).epi_f (h'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The dimension shift `Tor_{n+1}(X₃, Q) ≅ Tor_n(X₁, Q)` in the derived variable. -/
def tor'δFirstIso (hS : S.ShortExact) (Q : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor' (ModuleCat.{u} R) (n + 1)).obj S.X₂).obj Q))
    (h' : IsZero (((Tor' (ModuleCat.{u} R) n).obj S.X₂).obj Q)) :
    ((Tor' (ModuleCat.{u} R) (n + 1)).obj S.X₃).obj Q ≅
      ((Tor' (ModuleCat.{u} R) n).obj S.X₁).obj Q :=
  haveI := isIso_Tor'δFirst hS Q n h h'
  asIso (Stacks.Tor.Tor'δFirst hS Q n)

/-- `Tor₁(X₃, Q)` is the kernel of `X₁ ⊗ Q → X₂ ⊗ Q` as soon as `Tor₁(X₂, Q)` vanishes. -/
def tor'OneIsoKernel (hS : S.ShortExact) (Q : ModuleCat.{u} R)
    (h : IsZero (((Tor' (ModuleCat.{u} R) 1).obj S.X₂).obj Q)) :
    ((Tor' (ModuleCat.{u} R) 1).obj S.X₃).obj Q ≅ kernel (S.f ▷ Q) := by
  have hex := Stacks.Tor.Tor'_composableArrows_exact_first_zero hS Q
  let T : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (Stacks.Tor.Tor'δFirstZero hS Q) (S.f ▷ Q) (hex.toIsComplex.zero 2)
  haveI : Mono T.f := Stacks.Tor.mono_Tor'δFirstZero hS Q h
  have hT : T.Exact := hex.exact' 2 3 4
  exact IsLimit.conePointUniqueUpToIso hT.fIsKernel (limit.isLimit (parallelPair (S.f ▷ Q) 0))

end Shift

section Twist

variable {R B : Type u} [CommRing R] [CommRing B]

/-- A `B`-module `P` regarded as an `R`-module through a ring map `f : R →+* B`, keeping its
`B`-module structure. This is a type synonym, so that a `B`-module can carry the two `R`-module
structures coming from two different ring maps `R →+* B` without a diamond. -/
def Twist (_f : R →+* B) (P : Type u) : Type u := P

namespace Twist

variable (f : R →+* B) (P : Type u) [AddCommGroup P] [Module B P]

/-- The additive group structure of the twist is that of `P`. -/
instance : AddCommGroup (Twist f P) := ‹AddCommGroup P›

/-- The `B`-module structure of the twist is that of `P`. -/
instance : Module B (Twist f P) := ‹Module B P›

/-- The `R`-module structure of the twist: `r` acts as `f r`. -/
instance : Module R (Twist f P) := Module.compHom P f

/-- The identity of the underlying type, from `P` to its twist. -/
def of : P ≃ₗ[B] Twist f P := LinearEquiv.refl B P

/-- An element of `P`, regarded as an element of its twist. -/
def mk {P : Type u} (x : P) : Twist f P := x

variable {f P} in
omit [Module B P] in
/-- `mk` sends `0` to `0`. -/
theorem mk_zero : mk f (0 : P) = 0 := rfl

variable {f P} in
omit [Module B P] in
/-- `mk` is additive. -/
theorem mk_add (x y : P) : mk f x + mk f y = mk f (x + y) := rfl

variable {f P} in
/-- `mk` commutes with the action of `B`. -/
theorem smul_mk (b : B) (x : P) : b • mk f x = mk f (b • x) := rfl

variable {f P} in
/-- An element `r` of `R` acts on `mk f x` as `f r` acts on `x`. -/
theorem rsmul_mk (r : R) (x : P) : r • mk f x = mk f (f r • x) := rfl

/-- An element `r` of `R` acts on the twist as `f r`. -/
theorem smul_def (r : R) (x : Twist f P) : r • x = f r • x := rfl

/-- The actions of `B` and `R` on the twist commute. -/
instance : SMulCommClass B R (Twist f P) where
  smul_comm b r x := by
    rw [smul_def, smul_def, smul_smul, smul_smul, mul_comm]

/-- The actions of `R` and `B` on the twist commute. -/
instance : SMulCommClass R B (Twist f P) := SMulCommClass.symm B R (Twist f P)

/-- A `B`-linear equivalence induces an `R`-linear equivalence of the twists. -/
def congr {f : R →+* B} {P P' : Type u} [AddCommGroup P] [Module B P] [AddCommGroup P']
    [Module B P'] (e : P ≃ₗ[B] P') : Twist f P ≃ₗ[R] Twist f P' where
  toFun := e
  invFun := e.symm
  map_add' := e.map_add
  map_smul' r x := e.map_smul (f r) x
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- A flat ring map makes its target a flat module, twisted. -/
theorem flat_of_ringHomFlat {f : R →+* B} (hf : f.Flat) : Module.Flat R (Twist f B) := by
  let := f.toAlgebra
  have : Module.Flat R B := hf
  exact Module.Flat.of_linearEquiv (M := B) (N := Twist f B)
    { toFun x := (x : B)
      invFun x := x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **The length of a twist.** If every element of `B` acts on `T` through an element of `R`, then
the length of `T` over `B` is its length over `R` through `f`. -/
theorem length_eq (f : R →+* B) (T : Type u) [AddCommGroup T] [Module B T]
    (hT : ∀ b : B, ∃ r : R, ∀ t : T, b • t = f r • t) :
    Module.length R (Twist f T) = Module.length B T := by
  refine le_antisymm ?_ (Module.length_le_length_restrictScalars R B f T)
  let g : Submodule R (Twist f T) → Submodule B T := fun N =>
    { carrier := (N : Set (Twist f T))
      add_mem' := N.add_mem
      zero_mem' := N.zero_mem
      smul_mem' := fun b t ht => by
        obtain ⟨r, hr⟩ := hT b
        rw [hr]
        exact N.smul_mem r ht }
  exact WithBot.unbot_mono _ _ (Order.krullDim_le_of_strictMono g
    fun _ _ hab => ⟨fun _ hx => hab.le hx, fun h => hab.not_ge fun _ hx => h hx⟩)

end Twist

end Twist

section Kernel

variable {R : Type u} [CommRing R] {A A' C C' : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup A'] [Module R A'] [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']

/-- The kernels of two linear maps intertwined by linear equivalences are equivalent. -/
def kerEquivOfComm (φ : A →ₗ[R] C) (ψ : A' →ₗ[R] C') (e₁ : A ≃ₗ[R] A') (e₂ : C ≃ₗ[R] C')
    (h : ∀ x, e₂ (φ x) = ψ (e₁ x)) : LinearMap.ker φ ≃ₗ[R] LinearMap.ker ψ where
  toFun x := ⟨e₁ x, by rw [LinearMap.mem_ker, ← h, LinearMap.mem_ker.mp x.2, map_zero]⟩
  invFun y := ⟨e₁.symm y, by
    rw [LinearMap.mem_ker, ← e₂.map_eq_zero_iff, h, e₁.apply_symm_apply]
    exact LinearMap.mem_ker.mp y.2⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp
  left_inv x := by ext; simp
  right_inv y := by ext; simp

end Kernel

section Contraction

variable {R B : Type u} [CommRing R] [CommRing B] (α : R →+* B) (π : B →+* R)
  (hα : ∀ r, π (α r) = r)

/-- The contraction `B ⊗_R M → M`, `b ⊗ m ↦ π(b) m`, for a retraction `π` of `α`. -/
def contract (M : Type u) [AddCommGroup M] [Module R M] : Twist α B ⊗[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun b := π (show B from b) • LinearMap.id
      map_add' b b' := by
        change π ((show B from b) + (show B from b')) • _ = _
        rw [map_add, add_smul]
      map_smul' r b := by
        change π (α r * (show B from b)) • _ = r • π (show B from b) • _
        rw [map_mul, hα, mul_smul] }

/-- The contraction sends `b ⊗ m` to `π(b) m`. -/
@[simp]
theorem contract_tmul (M : Type u) [AddCommGroup M] [Module R M] (b : B) (m : M) :
    contract α π hα M (Twist.mk α b ⊗ₜ m) = π b • m := rfl

/-- The contraction is semilinear along `π`: `contract (b • x) = π(b) • contract x`. -/
theorem contract_smul (M : Type u) [AddCommGroup M] [Module R M] (b : B)
    (x : Twist α B ⊗[R] M) : contract α π hα M (b • x) = π b • contract α π hα M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b' m =>
    rw [TensorProduct.smul_tmul']
    show π (b * (show B from b')) • m = π b • π (show B from b') • m
    rw [map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

end Contraction

section Pair

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B)

/-- The base change `B ⊗_{R, α} M` of an `R`-module along `α`, as a `B`-module. -/
abbrev Ext (M : Type u) [AddCommGroup M] [Module R M] : Type u := Twist α B ⊗[R] M

/-- The `B`-module `(B ⊗_{R, α} M) ⊗_{R, β} N`: the base change of `M` along `α`, regarded as an
`R`-module through `β`, tensored with `N`. For `B = K[[x, y]]` and `α`, `β` the inclusions of the
two sets of variables this is the complete tensor product `M ⊗̂_K N`. -/
abbrev Pair (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Type u :=
  Twist β (Ext α M) ⊗[R] N

variable {M M' N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- The base change of a linear map, `B`-linearly. -/
def extMap (f : M →ₗ[R] M') : Ext α M →ₗ[B] Ext α M' where
  toFun := LinearMap.lTensor (Twist α B) f
  map_add' := map_add _
  map_smul' b x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' m => rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The base change of `f` sends `b ⊗ m` to `b ⊗ f m`. -/
@[simp]
theorem extMap_tmul (f : M →ₗ[R] M') (b : Twist α B) (m : M) :
    extMap α f (b ⊗ₜ m) = b ⊗ₜ f m := rfl

/-- A `B`-linear map between twists along `β` is `R`-linear. -/
def twistMap {P P' : Type u} [AddCommGroup P] [Module B P] [AddCommGroup P'] [Module B P']
    (g : P →ₗ[B] P') : Twist β P →ₗ[R] Twist β P' where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := g.map_smul (β r) x

/-- The functoriality of `Pair` in both variables. -/
def pairMap (f : M →ₗ[R] M') (g : N →ₗ[R] N') : Pair α β M N →ₗ[B] Pair α β M' N' where
  toFun := TensorProduct.map (twistMap β (extMap α f)) g
  map_add' := map_add _
  map_smul' b x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y n =>
      change TensorProduct.map (twistMap β (extMap α f)) g ((b • y) ⊗ₜ n) = _
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, RingHom.id_apply,
        TensorProduct.smul_tmul']
      congr 1
      exact (extMap α f).map_smul b y
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `pairMap f g` sends `y ⊗ n` to `extMap f y ⊗ g n`. -/
@[simp]
theorem pairMap_tmul (f : M →ₗ[R] M') (g : N →ₗ[R] N') (y : Twist β (Ext α M)) (n : N) :
    pairMap α β f g (y ⊗ₜ n) = (show Twist β (Ext α M') from extMap α f y) ⊗ₜ g n := rfl

end Pair

section Diagonal

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B) (π : B →+* R)
  (hα : ∀ r, π (α r) = r) (hβ : ∀ r, π (β r) = r)

/-- The quotient `B ⧸ ker π`, the structure ring of the diagonal. -/
abbrev Diag : Type u := B ⧸ RingHom.ker π

/-- The retraction `B ⧸ ker π → R` induced by `π`. -/
def diagRetraction : Diag π →+* R := Ideal.Quotient.lift (RingHom.ker π) π fun _ h => h

/-- The induced retraction sends the class of `b` to `π b`. -/
@[simp]
theorem diagRetraction_mk (b : B) : diagRetraction π (Ideal.Quotient.mk _ b) = π b := rfl

/-- The induced retraction is semilinear along `π`. -/
theorem diagRetraction_smul (b : B) (q : Diag π) :
    diagRetraction π (b • q) = π b * diagRetraction π q := by
  induction q using Quotient.inductionOn' with
  | h c => exact map_mul π b c

/-- In `B ⧸ ker π`, the class of `α (π b)` is the class of `b`. -/
theorem mk_map_eq (hα : ∀ r, π (α r) = r) (b : B) :
    (Ideal.Quotient.mk (RingHom.ker π) (α (π b)) : Diag π) =
    Ideal.Quotient.mk (RingHom.ker π) b := by
  rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, hα, sub_self]

/-- Two sections `α`, `β` of `π` agree modulo `ker π`. -/
theorem mk_eq_mk_of_retraction (hα : ∀ r, π (α r) = r) (hβ : ∀ r, π (β r) = r) (r : R) :
    (Ideal.Quotient.mk (RingHom.ker π) (α r) : Diag π) =
      Ideal.Quotient.mk (RingHom.ker π) (β r) := by
  rw [← mk_map_eq α π hα (β r), hβ]

variable {M M' N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- The contraction `(B ⊗_{R, α} M) → M` is `R`-linear for the action of `R` through `β`. -/
def contractTwist (M : Type u) [AddCommGroup M] [Module R M] : Twist β (Ext α M) →ₗ[R] M where
  toFun x := contract α π hα M (show Ext α M from x)
  map_add' x y := map_add (contract α π hα M) (show Ext α M from x) y
  map_smul' r x := by
    change contract α π hα M (β r • (show Ext α M from x)) = r • contract α π hα M x
    rw [contract_smul, hβ]

/-- The contraction `(B ⊗_{R, α} M) ⊗_{R, β} N → M ⊗_R N`. -/
def contractPair (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Pair α β M N →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (contractTwist α β π hα hβ M) LinearMap.id

/-- The contraction `contractPair` is semilinear along `π`. -/
theorem contractPair_smul (b : B) (z : Pair α β M N) :
    contractPair α β π hα hβ M N (b • z) = π b • contractPair α β π hα hβ M N z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    rw [TensorProduct.smul_tmul']
    show (contract α π hα M (b • (show Ext α M from y))) ⊗ₜ n =
      π b • ((contract α π hα M y) ⊗ₜ n)
    rw [contract_smul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The forward map `((B ⊗_{R, α} M) ⊗_{R, β} N) ⊗_B (B ⧸ ker π) → M ⊗_R N`. -/
def diagFwd (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Pair α β M N ⊗[B] Diag π →+ M ⊗[R] N :=
  TensorProduct.liftAddHom
    { toFun z :=
        { toFun q := diagRetraction π q • contractPair α β π hα hβ M N z
          map_zero' := by rw [map_zero, zero_smul]
          map_add' q q' := by rw [map_add, add_smul] }
      map_zero' := by ext q; simp
      map_add' z z' := by ext q; simp }
    (fun b z q => by
      change diagRetraction π q • contractPair α β π hα hβ M N (b • z) =
        diagRetraction π (b • q) • contractPair α β π hα hβ M N z
      rw [contractPair_smul, diagRetraction_smul, smul_smul, mul_comm])

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- The forward map sends `z ⊗ q` to `π(q) • contractPair z`. -/
theorem diagFwd_tmul (z : Pair α β M N) (q : Diag π) :
    diagFwd α β π hα hβ M N (z ⊗ₜ q) = diagRetraction π q • contractPair α β π hα hβ M N z :=
  rfl

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- The forward map is semilinear along `π`. -/
theorem diagFwd_smul (b : B) (z : Pair α β M N ⊗[B] Diag π) :
    diagFwd α β π hα hβ M N (b • z) = π b • diagFwd α β π hα hβ M N z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [TensorProduct.smul_tmul', diagFwd_tmul, diagFwd_tmul, contractPair_smul, smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The element `((1 ⊗ m) ⊗ n)` of `(B ⊗_{R, α} M) ⊗_{R, β} N`. -/
def unitPair (m : M) (n : N) : Pair α β M N :=
  Twist.mk β (Twist.mk α (1 : B) ⊗ₜ m : Ext α M) ⊗ₜ n

/-- The contraction sends `(1 ⊗ m) ⊗ n` to `m ⊗ n`. -/
theorem contractPair_unitPair (m : M) (n : N) :
    contractPair α β π hα hβ M N (unitPair α β m n) = m ⊗ₜ n := by
  show (π 1 • m) ⊗ₜ n = m ⊗ₜ n
  rw [map_one, one_smul]

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- `(1 ⊗ r m) ⊗ n = α(r) • ((1 ⊗ m) ⊗ n)`. -/
theorem unitPair_smul_left (r : R) (m : M) (n : N) :
    unitPair α β (r • m) n = α r • unitPair α β m n := by
  unfold unitPair
  rw [TensorProduct.smul_tmul', Twist.smul_mk, ← TensorProduct.smul_tmul, Twist.rsmul_mk,
    TensorProduct.smul_tmul']
  rfl

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- `(1 ⊗ m) ⊗ r n = β(r) • ((1 ⊗ m) ⊗ n)`. -/
theorem unitPair_smul_right (r : R) (m : M) (n : N) :
    unitPair α β m (r • n) = β r • unitPair α β m n := by
  unfold unitPair
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Twist.rsmul_mk, TensorProduct.smul_tmul']
  rfl

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- `unitPair` is additive in its first argument. -/
theorem unitPair_add_left (m m' : M) (n : N) :
    unitPair α β (m + m') n = unitPair α β m n + unitPair α β m' n := by
  unfold unitPair
  rw [TensorProduct.tmul_add, ← Twist.mk_add, TensorProduct.add_tmul]

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- `unitPair` is additive in its second argument. -/
theorem unitPair_add_right (m : M) (n n' : N) :
    unitPair α β m (n + n') = unitPair α β m n + unitPair α β m n' := by
  unfold unitPair
  rw [TensorProduct.tmul_add]

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- In `Pair α β M N ⊗_B (B ⧸ ker π)`, `(x • p) ⊗ 1 = p ⊗ [x]`. -/
theorem smul_tmul_one_eq (x : B) (p : Pair α β M N) :
    (x • p) ⊗ₜ[B] (1 : Diag π) = p ⊗ₜ (Ideal.Quotient.mk (RingHom.ker π) x) := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

/-- The inverse map `M ⊗_R N → ((B ⊗_{R, α} M) ⊗_{R, β} N) ⊗_B (B ⧸ ker π)`,
`m ⊗ n ↦ ((1 ⊗ m) ⊗ n) ⊗ 1`. -/
def diagInv (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    M ⊗[R] N →ₗ[R] Twist β (Pair α β M N ⊗[B] Diag π) :=
  TensorProduct.lift (LinearMap.mk₂ R
    (fun m n => Twist.mk β (unitPair α β m n ⊗ₜ[B] (1 : Diag π)))
    (fun m m' n => by
      rw [Twist.mk_add, ← TensorProduct.add_tmul, unitPair_add_left])
    (fun r m n => by
      rw [Twist.rsmul_mk, TensorProduct.smul_tmul', unitPair_smul_left, smul_tmul_one_eq,
        smul_tmul_one_eq, mk_eq_mk_of_retraction α β π hα hβ])
    (fun m n n' => by
      rw [Twist.mk_add, ← TensorProduct.add_tmul, unitPair_add_right])
    (fun r m n => by
      rw [Twist.rsmul_mk, TensorProduct.smul_tmul', unitPair_smul_right]))

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- The inverse map sends `m ⊗ n` to `((1 ⊗ m) ⊗ n) ⊗ 1`. -/
theorem diagInv_tmul (m : M) (n : N) :
    diagInv α β π hα hβ M N (m ⊗ₜ n) = Twist.mk β (unitPair α β m n ⊗ₜ[B] (1 : Diag π)) := rfl

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- `(b ⊗ m) ⊗ n = b • ((1 ⊗ m) ⊗ n)`. -/
theorem tmul_tmul_eq_smul_unitPair (b : B) (m : M) (n : N) :
    (Twist.mk β (Twist.mk α b ⊗ₜ m : Ext α M) ⊗ₜ n : Pair α β M N) = b • unitPair α β m n := by
  unfold unitPair
  rw [TensorProduct.smul_tmul', Twist.smul_mk, TensorProduct.smul_tmul', Twist.smul_mk,
    smul_eq_mul, mul_one]

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- The forward map sends `((1 ⊗ m) ⊗ n) ⊗ [x]` to `π(x) • (m ⊗ n)`. -/
theorem diagFwd_unitPair_tmul (m : M) (n : N) (x : B) :
    diagFwd α β π hα hβ M N (unitPair α β m n ⊗ₜ Ideal.Quotient.mk (RingHom.ker π) x) =
      π x • (m ⊗ₜ n) := by
  rw [diagFwd_tmul, contractPair_unitPair, diagRetraction_mk]

omit [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] in
/-- The inverse map sends `π(x) • (m ⊗ n)` to `((1 ⊗ m) ⊗ n) ⊗ [x]`. -/
theorem diagInv_smul_tmul (m : M) (n : N) (x : B) :
    diagInv α β π hα hβ M N (π x • (m ⊗ₜ n)) =
      Twist.mk β (unitPair α β m n ⊗ₜ Ideal.Quotient.mk (RingHom.ker π) x) := by
  rw [map_smul, diagInv_tmul, Twist.rsmul_mk, TensorProduct.smul_tmul', smul_tmul_one_eq,
    mk_map_eq β π hβ]

/-- **The degree-zero reduction to the diagonal**:
`((B ⊗_{R, α} M) ⊗_{R, β} N) ⊗_B (B ⧸ ker π) ≅ M ⊗_R N`, `R`-linearly for the action of `R`
through `β`. -/
def diagEquiv (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Twist β (Pair α β M N ⊗[B] Diag π) ≃ₗ[R] M ⊗[R] N where
  toFun z := diagFwd α β π hα hβ M N z
  map_add' z z' := map_add (diagFwd α β π hα hβ M N) z z'
  map_smul' r z := (diagFwd_smul α β π hα hβ (β r) z).trans (by rw [hβ]; rfl)
  invFun := diagInv α β π hα hβ M N
  left_inv z := by
    change diagInv α β π hα hβ M N (diagFwd α β π hα hβ M N z) = Twist.mk β z
    induction z using TensorProduct.induction_on with
    | zero => simp; rfl
    | tmul p q =>
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
      induction p using TensorProduct.induction_on with
      | zero => simp; rfl
      | tmul y n =>
        obtain ⟨y, rfl⟩ : ∃ y' : Ext α M, Twist.mk β y' = y := ⟨y, rfl⟩
        induction y using TensorProduct.induction_on with
        | zero =>
          rw [Twist.mk_zero, TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero, map_zero]
          rfl
        | tmul b m =>
          obtain ⟨b, rfl⟩ : ∃ b' : B, Twist.mk α b' = b := ⟨b, rfl⟩
          rw [tmul_tmul_eq_smul_unitPair, TensorProduct.smul_tmul, Algebra.smul_def,
            Ideal.Quotient.algebraMap_eq, ← map_mul, diagFwd_unitPair_tmul, diagInv_smul_tmul]
          rfl
        | add y y' hy hy' =>
          rw [← Twist.mk_add, TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, map_add,
            hy, hy']
          rfl
      | add p p' hp hp' =>
        rw [TensorProduct.add_tmul, map_add, map_add, hp, hp']
        rfl
    | add z z' hz hz' =>
      rw [map_add, map_add, hz, hz']
      rfl
  right_inv x := by
    change diagFwd α β π hα hβ M N (diagInv α β π hα hβ M N x) = x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact map_zero _
    | tmul m n =>
      rw [diagInv_tmul]
      change diagFwd α β π hα hβ M N (unitPair α β m n ⊗ₜ[B] (1 : Diag π)) = _
      rw [diagFwd_tmul, contractPair_unitPair, map_one, one_smul]
    | add x y hx hy =>
      rw [map_add]
      exact (map_add (diagFwd α β π hα hβ M N) _ _).trans (by rw [hx, hy])

/-- The contraction is natural in `M`. -/
theorem contract_extMap (f : M →ₗ[R] M') (y : Ext α M) :
    contract α π hα M' (extMap α f y) = f (contract α π hα M y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    obtain ⟨b, rfl⟩ : ∃ b' : B, Twist.mk α b' = b := ⟨b, rfl⟩
    rw [extMap_tmul, contract_tmul, contract_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The contraction `contractPair` is natural in `M` and `N`. -/
theorem contractPair_pairMap (f : M →ₗ[R] M') (g : N →ₗ[R] N') (p : Pair α β M N) :
    contractPair α β π hα hβ M' N' (pairMap α β f g p) =
      TensorProduct.map f g (contractPair α β π hα hβ M N p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    obtain ⟨y, rfl⟩ : ∃ y' : Ext α M, Twist.mk β y' = y := ⟨y, rfl⟩
    rw [pairMap_tmul]
    show (contract α π hα M' (extMap α f y)) ⊗ₜ g n =
      TensorProduct.map f g ((contract α π hα M y) ⊗ₜ n)
    rw [contract_extMap, TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Naturality of the degree-zero reduction to the diagonal** in both variables. -/
theorem diagFwd_naturality (f : M →ₗ[R] M') (g : N →ₗ[R] N') (z : Pair α β M N ⊗[B] Diag π) :
    diagFwd α β π hα hβ M' N' (LinearMap.rTensor (Diag π) (pairMap α β f g) z) =
      TensorProduct.map f g (diagFwd α β π hα hβ M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    rw [LinearMap.rTensor_tmul, diagFwd_tmul, diagFwd_tmul, contractPair_pairMap, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Diagonal

section Free

variable {R B : Type u} [CommRing R] [CommRing B]

/-- `N ⊗_R R^ι ≅ N^ι`, linearly over a ring `B` acting on `N` and commuting with `R`. -/
def piScalarRightOver (N : Type u) [AddCommGroup N] [Module R N] [Module B N]
    [SMulCommClass R B N] (ι : Type) [Fintype ι] [DecidableEq ι] :
    N ⊗[R] (ι → R) ≃ₗ[B] (ι → N) :=
  { TensorProduct.piScalarRight R R N ι with
    map_smul' := fun b x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul n v =>
        ext j
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          TensorProduct.piScalarRight_apply, RingHom.id_apply, TensorProduct.smul_tmul',
          TensorProduct.piScalarRightHom_tmul, Pi.smul_apply]
        rw [smul_comm]
      | add x y hx hy =>
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply] at hx hy ⊢
        rw [smul_add, map_add, hx, hy, map_add, smul_add] }

end Free

section PairExact

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B)
variable {M M' M'' N N' N'' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup M''] [Module R M''] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
  [AddCommGroup N''] [Module R N'']

/-- The base change of the identity is the identity. -/
theorem extMap_id : extMap α (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  LinearMap.ext fun x => LinearMap.lTensor_id_apply _ _ x

/-- `pairMap` in the first variable preserves exactness of `M → M' → M'' → 0`. -/
theorem pairMap_left_exact {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''} (h : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (pairMap α β f (LinearMap.id : N →ₗ[R] N)) (pairMap α β g LinearMap.id) := by
  have h₁ : Function.Exact (twistMap β (extMap α f)) (twistMap β (extMap α g)) :=
    lTensor_exact (Twist α B) h hg
  have h₂ : Function.Surjective (twistMap β (extMap α g)) :=
    LinearMap.lTensor_surjective (Twist α B) hg
  exact rTensor_exact N h₁ h₂

/-- `pairMap` in the first variable preserves surjectivity. -/
theorem pairMap_left_surjective {g : M' →ₗ[R] M''} (hg : Function.Surjective g) :
    Function.Surjective (pairMap α β g (LinearMap.id : N →ₗ[R] N)) :=
  LinearMap.rTensor_surjective N (LinearMap.lTensor_surjective (Twist α B) hg)

/-- If `B` is flat over `R` through `α` and `N` is flat, `pairMap` in the first variable preserves
injectivity. -/
theorem pairMap_left_injective [Module.Flat R (Twist α B)] [Module.Flat R N] {f : M →ₗ[R] M'}
    (hf : Function.Injective f) :
    Function.Injective (pairMap α β f (LinearMap.id : N →ₗ[R] N)) := by
  have h₁ : Function.Injective (twistMap β (extMap α f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  exact Module.Flat.rTensor_preserves_injective_linearMap _ h₁

/-- `pairMap id g` is `lTensor g`. -/
theorem pairMap_right_eq (g : N →ₗ[R] N') :
    (pairMap α β (LinearMap.id : M →ₗ[R] M) g : Pair α β M N → Pair α β M N') =
      LinearMap.lTensor (Twist β (Ext α M)) g := by
  funext x
  show TensorProduct.map (twistMap β (extMap α LinearMap.id)) g x = _
  congr 1
  rw [extMap_id]
  rfl

/-- `pairMap` in the second variable preserves exactness of `N → N' → N'' → 0`. -/
theorem pairMap_right_exact {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''} (h : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Exact (pairMap α β (LinearMap.id : M →ₗ[R] M) f) (pairMap α β LinearMap.id g) := by
  rw [pairMap_right_eq, pairMap_right_eq]
  exact lTensor_exact _ h hg

/-- `pairMap` in the second variable preserves surjectivity. -/
theorem pairMap_right_surjective {g : N' →ₗ[R] N''} (hg : Function.Surjective g) :
    Function.Surjective (pairMap α β (LinearMap.id : M →ₗ[R] M) g) := by
  rw [pairMap_right_eq]
  exact LinearMap.lTensor_surjective _ hg

/-- If `B ⊗_{R, α} M` is flat over `R` through `β`, `pairMap` in the second variable preserves
injectivity. -/
theorem pairMap_right_injective [Module.Flat R (Twist β (Ext α M))] {f : N →ₗ[R] N'}
    (hf : Function.Injective f) :
    Function.Injective (pairMap α β (LinearMap.id : M →ₗ[R] M) f) := by
  rw [pairMap_right_eq]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Base change commutes with composition. -/
theorem extMap_extMap (f : M →ₗ[R] M') (f' : M' →ₗ[R] M'') (y : Ext α M) :
    extMap α f' (extMap α f y) = extMap α (f' ∘ₗ f) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `pairMap` commutes with composition in both variables. -/
theorem pairMap_pairMap (f : M →ₗ[R] M') (f' : M' →ₗ[R] M'') (g : N →ₗ[R] N')
    (g' : N' →ₗ[R] N'') (z : Pair α β M N) :
    pairMap α β f' g' (pairMap α β f g z) = pairMap α β (f' ∘ₗ f) (g' ∘ₗ g) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    obtain ⟨y, rfl⟩ : ∃ y' : Ext α M, Twist.mk β y' = y := ⟨y, rfl⟩
    rw [pairMap_tmul, pairMap_tmul, pairMap_tmul]
    congr 1
    exact extMap_extMap α f f' y
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `pairMap id id` is the identity. -/
theorem pairMap_id_apply (z : Pair α β M N) :
    pairMap α β (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y n =>
    obtain ⟨y, rfl⟩ : ∃ y' : Ext α M, Twist.mk β y' = y := ⟨y, rfl⟩
    rw [pairMap_tmul, extMap_id]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

end PairExact

section TorVanishing

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B) (π : B →+* R)
  (hα : ∀ r, π (α r) = r) (hβ : ∀ r, π (β r) = r)

/-- The `B`-module `(B ⊗_{R, α} R^j) ⊗_{R, β} R^m` is free. -/
theorem free_pair_pi (j m : ℕ) : Module.Free B (Pair α β (Fin j → R) (Fin m → R)) := by
  let e₁ : Ext α (Fin j → R) ≃ₗ[B] (Fin j → Twist α B) := piScalarRightOver _ _
  let e₂ : Pair α β (Fin j → R) (Fin m → R) ≃ₗ[B] (Fin m → Twist β (Ext α (Fin j → R))) :=
    piScalarRightOver _ _
  let e₃ : Twist β (Ext α (Fin j → R)) ≃ₗ[B] (Fin j → B) :=
    ((Twist.of β _).symm.trans e₁).trans
      (LinearEquiv.piCongrRight fun _ => (Twist.of α B).symm)
  exact Module.Free.of_equiv (e₂.trans (LinearEquiv.piCongrRight fun _ => e₃)).symm

/-- The `B`-module `(B ⊗_{R, α} R^j) ⊗_{R, β} R^m` is projective. -/
theorem projective_pair_pi (j m : ℕ) :
    Projective (ModuleCat.of B (Pair α β (Fin j → R) (Fin m → R))) := by
  have := free_pair_pi α β (R := R) (B := B) j m
  exact (ModuleCat.of B _).projective_of_categoryTheory_projective

/-- The short complex `0 → (B ⊗ M₁) ⊗ N → (B ⊗ M₂) ⊗ N → (B ⊗ M₃) ⊗ N → 0` of `B`-modules
attached to a complex `M₁ → M₂ → M₃` of `R`-modules. -/
def pairSCLeft (N : Type u) [AddCommGroup N] [Module R N] {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃]
    [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    (hg : Function.Surjective g) : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (ModuleCat.ofHom (pairMap α β f (LinearMap.id : N →ₗ[R] N)))
    (ModuleCat.ofHom (pairMap α β g (LinearMap.id : N →ₗ[R] N))) (by
      ext x
      exact (pairMap_left_exact α β h hg).apply_apply_eq_zero x)

/-- If `B` is flat over `R` through `α` and `N` is flat, `pairSCLeft` of a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` is short exact. -/
theorem pairSCLeft_shortExact [Module.Flat R (Twist α B)] (N : Type u) [AddCommGroup N]
    [Module R N] [Module.Flat R N] {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃]
    [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (pairSCLeft α β N f g h hg).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (pairMap_left_exact α β h hg)
    (pairMap_left_injective α β hf) (pairMap_left_surjective α β hg)

variable [IsNoetherianRing R] [Module.Flat R (Twist α B)]

include hα hβ in
/-- **The `Tor` modules of `(B ⊗_{R, α} M) ⊗_{R, β} R^m` against the diagonal vanish in positive
degrees**, for every finite `R`-module `M`. This is a dimension shift in `M` along a finite free
cover: the base change of a free module is free, and in degree one the contraction
`((B ⊗ M) ⊗ R^m) ⊗_B (B ⧸ ker π) ≅ M ⊗ R^m` turns the connecting map into an injection. -/
theorem isZero_tor'_pair_pi (k : ℕ) : ∀ (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (m : ℕ),
    IsZero (((Tor' (ModuleCat.{u} B) (k + 1)).obj
      (ModuleCat.of B (Pair α β M (Fin m → R)))).obj (ModuleCat.of B (Diag π))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro M _ _ _ m
    obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' R M
    let S := pairSCLeft α β (Fin m → R) (LinearMap.ker p).subtype p
      (LinearMap.exact_subtype_ker_map p) hp
    have hS : S.ShortExact := pairSCLeft_shortExact α β _ _ _ _ (Submodule.injective_subtype _) hp
    have : Projective S.X₂ := projective_pair_pi α β (R := R) (B := B) j m
    cases k with
    | zero =>
      have h1 : IsZero (((Tor' (ModuleCat.{u} B) 1).obj S.X₂).obj (ModuleCat.of B (Diag π))) :=
        isZero_Tor'_succ_of_projective _ _ _ 0
      refine IsZero.of_iso ?_ (tor'OneIsoKernel hS _ h1)
      have hmono : Mono (S.f ▷ ModuleCat.of B (Diag π)) := by
        rw [ModuleCat.mono_iff_injective]
        show Function.Injective (LinearMap.rTensor (Diag π)
          (pairMap α β (LinearMap.ker p).subtype (LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R))))
        intro x y hxy
        have key := congrArg (diagFwd α β π hα hβ (Fin j → R) (Fin m → R)) hxy
        rw [diagFwd_naturality, diagFwd_naturality] at key
        have hinj : Function.Injective (TensorProduct.map (LinearMap.ker p).subtype
            (LinearMap.id : (Fin m → R) →ₗ[R] (Fin m → R))) :=
          Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
        exact (diagEquiv α β π hα hβ (LinearMap.ker p) (Fin m → R)).injective (hinj key)
      exact isZero_kernel_of_mono _
    | succ k =>
      exact IsZero.of_iso (ih k k.lt_succ_self (LinearMap.ker p) m) (tor'δFirstIso hS _ (k + 1)
        (isZero_Tor'_succ_of_projective _ _ _ (k + 1)) (isZero_Tor'_succ_of_projective _ _ _ k))

end TorVanishing

section ReductionToDiagonal

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B) (π : B →+* R)
  (hα : ∀ r, π (α r) = r) (hβ : ∀ r, π (β r) = r)

/-- The short complex `0 → (B ⊗ M) ⊗ N₁ → (B ⊗ M) ⊗ N₂ → (B ⊗ M) ⊗ N₃ → 0` of `B`-modules
attached to a complex `N₁ → N₂ → N₃` of `R`-modules. -/
def pairSCRight (M : Type u) [AddCommGroup M] [Module R M] {N₁ N₂ N₃ : Type u}
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃]
    [Module R N₃] (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) (h : Function.Exact f g)
    (hg : Function.Surjective g) : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (ModuleCat.ofHom (pairMap α β (LinearMap.id : M →ₗ[R] M) f))
    (ModuleCat.ofHom (pairMap α β (LinearMap.id : M →ₗ[R] M) g)) (by
      ext x
      exact (pairMap_right_exact α β h hg).apply_apply_eq_zero x)

/-- If `B ⊗_{R, α} M` is flat over `R` through `β`, `pairSCRight` of a short exact sequence
`0 → N₁ → N₂ → N₃ → 0` is short exact. -/
theorem pairSCRight_shortExact (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Flat R (Twist β (Ext α M))] {N₁ N₂ N₃ : Type u}
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃]
    [Module R N₃] (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    (pairSCRight α β M f g h hg).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (pairMap_right_exact α β h hg)
    (pairMap_right_injective α β hf) (pairMap_right_surjective α β hg)

/-- The short complex `0 → ker p → R^j → N → 0` of a finite free cover. -/
def coverSC {N : Type u} [AddCommGroup N] [Module R N] {j : ℕ} (p : (Fin j → R) →ₗ[R] N) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker p).subtype) (ModuleCat.ofHom p) (by
    ext x
    exact x.2)

/-- For a surjection `p : R^j → N`, the complex `0 → ker p → R^j → N → 0` is short exact. -/
theorem coverSC_shortExact {N : Type u} [AddCommGroup N] [Module R N] {j : ℕ}
    (p : (Fin j → R) →ₗ[R] N) (hp : Function.Surjective p) : (coverSC p).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_ker_map p)
    (Submodule.injective_subtype _) hp

variable [IsNoetherianRing R] [Module.Flat R (Twist α B)]

omit [IsNoetherianRing R] [Module.Flat R (Twist α B)] in
/-- The forward map, followed by `M ⊗ N ≅ N ⊗ M`, is natural in `N`. -/
theorem comm_diagFwd_rTensor (M : Type u) [AddCommGroup M] [Module R M] {N₁ N₂ : Type u}
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂)
    (x : Pair α β M N₁ ⊗[B] Diag π) :
    TensorProduct.comm R M N₂ (diagFwd α β π hα hβ M N₂
        (LinearMap.rTensor (Diag π) (pairMap α β LinearMap.id f) x)) =
      LinearMap.rTensor M f (TensorProduct.comm R M N₁ (diagFwd α β π hα hβ M N₁ x)) := by
  rw [diagFwd_naturality]
  induction (diagFwd α β π hα hβ M N₁ x) using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

/-- The degree-one comparison of kernels. -/
def kerDiagEquiv (M : Type u) [AddCommGroup M] [Module R M] {N₁ N₂ : Type u}
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] (f : N₁ →ₗ[R] N₂) :
    LinearMap.ker (twistMap β (LinearMap.rTensor (Diag π)
        (pairMap α β (LinearMap.id : M →ₗ[R] M) f))) ≃ₗ[R]
      LinearMap.ker (LinearMap.rTensor M f) :=
  kerEquivOfComm _ _ ((diagEquiv α β π hα hβ M N₁).trans (TensorProduct.comm R M N₁))
    ((diagEquiv α β π hα hβ M N₂).trans (TensorProduct.comm R M N₂))
    (fun x => comm_diagFwd_rTensor α β π hα hβ M f x)

/-- The kernel of a `B`-linear map, twisted along `β`, is the kernel of the twisted map. -/
def twistKerEquiv {P P' : Type u} [AddCommGroup P] [Module B P] [AddCommGroup P'] [Module B P']
    (φ : P →ₗ[B] P') : Twist β (LinearMap.ker φ) ≃ₗ[R] LinearMap.ker (twistMap β φ) where
  toFun x := ⟨(x : LinearMap.ker φ).1, (x : LinearMap.ker φ).2⟩
  invFun y := (⟨y.1, y.2⟩ : LinearMap.ker φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

include hα hβ in
/-- **The reduction to the diagonal for `Tor`.** Let `α, β : R → B` be ring maps with a common
retraction `π : B → R`, with `B` flat over `R` through `α`, and let `M` be a finite `R`-module
such that `B ⊗_{R, α} M` is flat over `R` through `β`. Then for every finite `R`-module `N`
and every `i ≥ 1`,
`Tor_i^B((B ⊗_{R, α} M) ⊗_{R, β} N, B ⧸ ker π) ≅ Tor_i^R(N, M)`, `R`-linearly for the action
of `R` through `β`. This is a dimension shift in `N` along finite free covers, starting from the
vanishing `isZero_tor'_pair_pi` and the degree-zero isomorphism `diagEquiv`. -/
theorem nonempty_tor'_pair_equiv (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R (Twist β (Ext α M))] (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      Nonempty (Twist β (((Tor' (ModuleCat.{u} B) (n + 1)).obj
          (ModuleCat.of B (Pair α β M N))).obj (ModuleCat.of B (Diag π))) ≃ₗ[R]
        ((Tor' (ModuleCat.{u} R) (n + 1)).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N _ _ _
    obtain ⟨j, p, hp⟩ := Module.Finite.exists_fin' R N
    have hS := coverSC_shortExact p hp
    let S' := pairSCRight α β M (LinearMap.ker p).subtype p (LinearMap.exact_subtype_ker_map p) hp
    have hS' : S'.ShortExact :=
      pairSCRight_shortExact α β M _ _ _ (Submodule.injective_subtype _) hp
    have : Projective (coverSC p).X₂ :=
      (ModuleCat.of R (Fin j → R)).projective_of_categoryTheory_projective
    cases n with
    | zero =>
      have hB : IsZero (((Tor' (ModuleCat.{u} B) 1).obj S'.X₂).obj (ModuleCat.of B (Diag π))) :=
        isZero_tor'_pair_pi α β π hα hβ 0 M j
      have hR : IsZero (((Tor' (ModuleCat.{u} R) 1).obj (coverSC p).X₂).obj (ModuleCat.of R M)) :=
        isZero_Tor'_succ_of_projective _ _ _ 0
      let eB := (tor'OneIsoKernel hS' (ModuleCat.of B (Diag π)) hB ≪≫
        ModuleCat.kernelIsoKer _).toLinearEquiv
      let eR :=
        (tor'OneIsoKernel hS (ModuleCat.of R M) hR ≪≫ ModuleCat.kernelIsoKer _).toLinearEquiv
      exact ⟨(Twist.congr eB).trans ((twistKerEquiv β _).trans
        ((kerDiagEquiv α β π hα hβ M (LinearMap.ker p).subtype).trans eR.symm))⟩
    | succ n =>
      let eB := (tor'δFirstIso hS' (ModuleCat.of B (Diag π)) (n + 1)
        (isZero_tor'_pair_pi α β π hα hβ (n + 1) M j)
        (isZero_tor'_pair_pi α β π hα hβ n M j)).toLinearEquiv
      let eR := (tor'δFirstIso hS (ModuleCat.of R M) (n + 1)
        (isZero_Tor'_succ_of_projective _ _ _ (n + 1))
        (isZero_Tor'_succ_of_projective _ _ _ n)).toLinearEquiv
      obtain ⟨e⟩ := ih n n.lt_succ_self (LinearMap.ker p)
      exact ⟨(Twist.congr eB).trans (e.trans eR.symm)⟩

omit [IsNoetherianRing R] [Module.Flat R (Twist α B)] in
include hβ in
/-- A `B`-module annihilated by `ker π` is a module over `R` through `β` with the same length. -/
theorem length_twist_of_le_annihilator (T : Type u) [AddCommGroup T] [Module B T]
    (hT : RingHom.ker π ≤ Module.annihilator B T) :
    Module.length R (Twist β T) = Module.length B T :=
  Twist.length_eq β T fun b => ⟨π b, fun t => by
    have hmem : b - β (π b) ∈ Module.annihilator B T := hT (by
      rw [RingHom.mem_ker, map_sub, hβ, sub_self])
    rw [← sub_eq_zero, ← sub_smul]
    exact Module.mem_annihilator.mp hmem t⟩

omit [IsNoetherianRing R] [Module.Flat R (Twist α B)] in
/-- The ideal `ker π` annihilates the `B`-module `B ⧸ ker π`. -/
theorem ker_le_annihilator_diag : RingHom.ker π ≤ Module.annihilator B (Diag π) := by
  intro b hb
  rw [Module.mem_annihilator]
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hb

include hα hβ in
/-- **The reduction to the diagonal for lengths of `Tor`.** Under the hypotheses of
`nonempty_tor'_pair_equiv`, for all `i` the length over `B` of
`Tor_i^B(B ⧸ ker π, (B ⊗_{R, α} M) ⊗_{R, β} N)` is the length over `R` of `Tor_i^R(M, N)`. -/
theorem length_tor_diag_pair (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R (Twist β (Ext α M))] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (i : ℕ) :
    Module.length B (((Tor (ModuleCat.{u} B) i).obj (ModuleCat.of B (Diag π))).obj
        (ModuleCat.of B (Pair α β M N))) =
      Module.length R (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R N)) := by
  have hann : RingHom.ker π ≤ Module.annihilator B (((Tor (ModuleCat.{u} B) i).obj
      (ModuleCat.of B (Diag π))).obj (ModuleCat.of B (Pair α β M N))) := fun b hb =>
    mem_annihilator_tor_of_mem_annihilator _ _ i (ker_le_annihilator_diag π hb)
  let eB := ((torFlip_iso_Tor' B i).app (ModuleCat.of B (Pair α β M N))).app
    (ModuleCat.of B (Diag π))
  let eR := ((torFlip_iso_Tor' R i).app (ModuleCat.of R N)).app (ModuleCat.of R M)
  rw [← length_twist_of_le_annihilator β π hβ _ hann]
  refine ((Twist.congr (f := β) eB.toLinearEquiv).length_eq).trans
    (Eq.trans ?_ eR.toLinearEquiv.length_eq.symm)
  cases i with
  | zero =>
    let zB := (((tensoringRight (ModuleCat.{u} B)).obj
      (ModuleCat.of B (Diag π))).leftDerivedZeroIsoSelf.app (ModuleCat.of B (Pair α β M N)))
    let zR := (((tensoringRight (ModuleCat.{u} R)).obj
      (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app (ModuleCat.of R N))
    exact ((Twist.congr zB.toLinearEquiv).trans ((diagEquiv α β π hα hβ M N).trans
      ((TensorProduct.comm R M N).trans zR.toLinearEquiv.symm))).length_eq
  | succ n =>
    obtain ⟨e⟩ := nonempty_tor'_pair_equiv α β π hα hβ M n N
    exact e.length_eq

end ReductionToDiagonal

end Stacks.SerreIntersection
