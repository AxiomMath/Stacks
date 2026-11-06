module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Symmetric powers of a sheaf of modules, sectionwise, and their comparison map

Let `O` be a presheaf of commutative rings on a site and `F` a presheaf of `O`-modules. Stacks
Tag 01CG says that the degree-`n` symmetric power `Symⁿ F` of a sheaf of modules on a ringed
space is the **sheafification** of the presheaf

`U ↦ Symⁿ_{O(U)}(F(U))`.

This file builds that presheaf, builds its canonical comparison map to the degree-`n` piece of a
graded algebra carrying a pairwise-commuting degree-one generator, and proves the two families
of equations that characterize both — the restriction maps and the comparison map — on products
of degree-one generators. The sheafification statement itself, that the comparison map becomes
an isomorphism after sheafifying, is **not** proved here; see the implementation notes.

The algebraic input is a gap in Mathlib: there is no functoriality of `SymmetricAlgebra`
whatsoever, in either variable. `SymmetricAlgebra.mapₛₗ` supplies the semilinear base change
along a ring homomorphism, which is exactly what the restriction maps of a presheaf of modules
need, and `SymmetricAlgebra.liftComm` supplies the universal property of `SymmetricAlgebra` for
a target ring that is *not* commutative but whose relevant image is.

## Main definitions

* `SymmetricAlgebra.mapₛₗ`: base change of the symmetric algebra along a ring homomorphism
  `φ : R →+* S` and a `φ`-semilinear map `u : M →ₛₗ[φ] N`, as a ring homomorphism
  `SymmetricAlgebra R M →+* SymmetricAlgebra S N`, and `SymPow.symMapₛₗ`, its restriction to the
  degree-`n` pieces.
* `SymmetricAlgebra.liftComm`: the extension of a linear map `γ : M →ₗ[R] T` into a ring whose
  image consists of pairwise commuting elements to a ring homomorphism
  `SymmetricAlgebra R M →+* T`.
* `PresheafOfModules.symPow`: the presheaf of sectionwise symmetric powers, with
  `PresheafOfModules.symPowSections` the sectionwise identification of its sections with
  `Symⁿ_{O(U)}(F(U))`.
* `Stacks.GradedAlgebra.homogeneousProd`: the ordered product of `n` degree-one local sections of
  a graded algebra, as a homogeneous section of degree `n`.
* `Stacks.GradedAlgebra.cmp`: the comparison morphism `symPow n F ⟶ Pc n` out of the presheaf of
  sectionwise symmetric powers into the degree-`n` piece of a graded algebra of presheaves of
  modules equipped with a pairwise-commuting degree-one generator, and
  `SheafOfModules.GradedAlgebra.symPowCmp`, the same for a sheaf of graded algebras.
* `SheafOfModules.GradedAlgebra.ringSheafOfIsSheaf`: a presheaf of commutative rings whose
  underlying presheaf of rings is a sheaf, read as a sheaf of rings, keeping that presheaf
  syntactically `O ⋙ forget₂ CommRingCat RingCat`.

## Main results

* `SymPow.ext_of_prod_ι`: two semilinear maps out of `Symⁿ` agreeing on the products of `n`
  degree-one generators are equal. With `SymmetricAlgebra.prod_ι_mem` this is what makes a
  specification *on products of generators* — the form in which Tag 01CG states both of its
  equation families — determine a map.
* `PresheafOfModules.symPowSections_map_prod_ι`: the restriction maps of `symPow n F` carry the
  product of the generators `s i` to the product of the generators `F.map f (s i)`.
* `Stacks.GradedAlgebra.cmpSections_prod_ι` and
  `SheafOfModules.GradedAlgebra.incl_symPowCmp_prod_ι`: the comparison map carries the product of
  the generators `s i` to their ordered product in the graded algebra.
* `Stacks.GradedAlgebra.cmpSections_naturality`: the comparison map is a morphism of presheaves
  of modules, which is what `Stacks.GradedAlgebra.cmp` bundles.

## Implementation notes

**What is here and what is not.** Tag 01CG is the conjunction of three assertions about the
presheaf `U ↦ Symⁿ_{O(U)}(F(U))`: the equations fixing its restriction maps, the equations fixing
the comparison map to `Symⁿ F`, and the assertion that the comparison map becomes an isomorphism
after sheafification. The first two are proved here, for an arbitrary graded algebra with a
pairwise-commuting degree-one generator — which is more general than the source, since no
universal property of the graded algebra is used. The third is not: it needs the sheafification
of `n ↦ symPow n F` to be assembled into a *sheaf of graded algebras* and shown to satisfy
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`, from which the comparison with any other
symmetric algebra of `F` follows by `IsUniversal.pieceIso`. Nothing in this file is specialized
in anticipation of that; it is the missing piece, not a modification of these.

**Universes.** The ring universe `w` and the module universe are *not* independent, and that is
forced rather than chosen: `SymmetricAlgebra R M` for `R : Type w` and `M : Type a` lives in
`Type (max w a)`, so the symmetric powers of a presheaf of modules in universe `a` form a
presheaf of modules in universe `max w a`, and a comparison map to a graded piece requires that
piece to be in the same universe as the symmetric powers. Everything here is therefore stated
for modules in `max w a` with `w` the universe of the ring, which is the most general form in
which the comparison typechecks; `a = w` recovers the equal-universe case, which is the one Tag
01CG is stated in.

**The two scalar structures on a ring of sections.** The base is a presheaf of *commutative*
rings `O`, and the ring presheaf is `O ⋙ forget₂ CommRingCat RingCat`. The `CommRing` instance on
its sections is the one from `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`; without that
import, `SymmetricAlgebra` cannot even be formed over a ring of sections. See the implementation
notes of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor` for the same point.

**The base of the sheaf-level section.** `ringSheafOfIsSheaf` is used rather than
`CategoryTheory.Sheaf.toRingCat` because the latter demands a sheaf of *commutative* rings plus
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`, while nothing here needs more than that the
underlying presheaf of rings is a sheaf; using it would strengthen the hypotheses.
`ringSheafOfIsSheaf_eq_toRingCat` proves the two coincide on the nose, so a consumer holding a
`toRingCat` — as the ringed-space case does, `structureSheafRing X` being
`toRingCat _ X.sheaf` — can use these results directly.

**`homogeneousProd` multiplies on the right.** The recursion `Symⁿ⁺¹ = Symⁿ · Sym¹` gives a
result of degree `(n : ℤ) + 1`, which is *definitionally* `((n + 1 : ℕ) : ℤ)`; the left-handed
recursion gives `1 + (n : ℤ)`, which is not, and forces a transport along `Int.add_comm` into
every statement about the product. The two products agree — they are both
`List.prod (List.ofFn ...)` in the ungraded realization — but only the right-handed one is
transport-free, and `Stacks.GradedAlgebra.incl_homogeneousProd` gives the transport-free
characterization that identifies either of them.

**Why `liftComm` rather than `SymmetricAlgebra.lift`.** The ungraded realization
`Stacks.GradedAlgebra.Total` of a graded algebra is not commutative: only the degree-one sections
in the image of the generator commute, and only by hypothesis. `SymmetricAlgebra.lift` needs a
commutative target, so `liftComm` factors through the commutative subalgebra generated by that
image. Its statement is existential (`SymmetricAlgebra.exists_liftComm`) so that the
`Algebra R T` structure `r ↦ r • 1` used in the construction, which is not an instance and not
canonical, stays inside the proof.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/
@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace SymmetricAlgebra

/-! ### Base change of the symmetric algebra along a ring homomorphism -/

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module S N]

/-- `SymmetricAlgebra S N` viewed as an `R`-algebra by restricting scalars along a ring
homomorphism `φ : R →+* S`.

This is deliberately not an instance: it depends on `φ`, and for `R = S` it would be a second
`Algebra R (SymmetricAlgebra R N)` structure competing with the canonical one. -/
@[instance_reducible]
noncomputable def algebraOfRingHom (φ : R →+* S) : Algebra R (SymmetricAlgebra S N) :=
  ((algebraMap S (SymmetricAlgebra S N)).comp φ).toAlgebra

/-- The degree-one generator of `SymmetricAlgebra S N`, read along a semilinear map
`u : M →ₛₗ[φ] N` as an `R`-linear map on `M`, where `R` acts through `φ`. -/
noncomputable def ιCompₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    letI := algebraOfRingHom (N := N) φ
    M →ₗ[R] SymmetricAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  { toFun := fun m => SymmetricAlgebra.ι S N (u m)
    map_add' := fun m m' => by rw [map_add, map_add]
    map_smul' := fun r m => by
      change SymmetricAlgebra.ι S N (u (r • m)) = r • SymmetricAlgebra.ι S N (u m)
      rw [map_smulₛₗ, map_smul, Algebra.smul_def, Algebra.smul_def]
      rfl }

/-- **Base change of the symmetric algebra.** A ring homomorphism `φ : R →+* S` together with a
`φ`-semilinear map `u : M →ₛₗ[φ] N` induces a ring homomorphism
`SymmetricAlgebra R M →+* SymmetricAlgebra S N` carrying `ι R M m` to `ι S N (u m)`. -/
@[ega "II 1.7.1" "partial", ega "II 1.7.2", ega "II 4.1.2" "special case"]
noncomputable def mapₛₗ (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  letI := algebraOfRingHom (N := N) φ
  (SymmetricAlgebra.lift (ιCompₛₗ φ u)).toRingHom

/-- `mapₛₗ φ u` sends the generator `ι R M m` to `ι S N (u m)`. -/
@[simp]
theorem mapₛₗ_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) (m : M) :
    mapₛₗ φ u (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (u m) :=
  let := algebraOfRingHom (N := N) φ
  SymmetricAlgebra.lift_ι_apply (ιCompₛₗ φ u) m

/-- `mapₛₗ φ u` restricts to `φ` on the image of the base ring. -/
@[simp]
theorem mapₛₗ_algebraMap (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) :
    mapₛₗ φ u (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (φ r) :=
  let := algebraOfRingHom (N := N) φ
  (SymmetricAlgebra.lift (ιCompₛₗ φ u)).commutes r

/-- Two ring homomorphisms out of a symmetric algebra agree as soon as they agree on the image
of the base ring and on the degree-one generators. -/
theorem ringHom_ext {T : Type*} [Semiring T] {f g : SymmetricAlgebra R M →+* T}
    (h₁ : ∀ r : R, f (algebraMap R (SymmetricAlgebra R M) r) =
      g (algebraMap R (SymmetricAlgebra R M) r))
    (h₂ : ∀ m : M, f (SymmetricAlgebra.ι R M m) = g (SymmetricAlgebra.ι R M m)) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `mapₛₗ φ u` is `φ`-semilinear: `mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x`. -/
theorem mapₛₗ_smul (φ : R →+* S) (u : M →ₛₗ[φ] N) (r : R) (x : SymmetricAlgebra R M) :
    mapₛₗ φ u (r • x) = φ r • mapₛₗ φ u x := by
  rw [Algebra.smul_def, map_mul, mapₛₗ_algebraMap, Algebra.smul_def]

/-- Base change along a composite: if `χ = ψ ∘ φ` and `v = w ∘ u` pointwise, then
`mapₛₗ χ v = mapₛₗ ψ w ∘ mapₛₗ φ u`. -/
@[ega "II 1.7.1" "partial"]
theorem mapₛₗ_eq_comp {T : Type*} [CommRing T] {P : Type*} [AddCommGroup P] [Module T P]
    {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (u : M →ₛₗ[φ] N) (w : N →ₛₗ[ψ] P)
    (v : M →ₛₗ[χ] P) (hχ : ∀ r, χ r = ψ (φ r)) (hv : ∀ m, v m = w (u m))
    (x : SymmetricAlgebra R M) : mapₛₗ χ v x = mapₛₗ ψ w (mapₛₗ φ u x) :=
  congrFun (congrArg (fun g : SymmetricAlgebra R M →+* SymmetricAlgebra T P => g.toFun)
    (ringHom_ext (f := mapₛₗ χ v) (g := (mapₛₗ ψ w).comp (mapₛₗ φ u))
      (fun r => by rw [mapₛₗ_algebraMap, RingHom.comp_apply, mapₛₗ_algebraMap, mapₛₗ_algebraMap,
        hχ])
      fun m => by rw [mapₛₗ_ι, RingHom.comp_apply, mapₛₗ_ι, mapₛₗ_ι, hv])) x

/-- Base change along the identity, in the propositional form the functoriality law of a
presheaf of modules provides. -/
theorem mapₛₗ_eq_self {φ : R →+* R} (u : M →ₛₗ[φ] M) (hφ : ∀ r, φ r = r) (hu : ∀ m, u m = m)
    (x : SymmetricAlgebra R M) : mapₛₗ φ u x = x :=
  congrFun (congrArg (fun g : SymmetricAlgebra R M →+* SymmetricAlgebra R M => g.toFun)
    (ringHom_ext (f := mapₛₗ φ u) (g := RingHom.id (SymmetricAlgebra R M))
      (fun r => by rw [mapₛₗ_algebraMap, hφ]; rfl) fun m => by rw [mapₛₗ_ι, hu]; rfl)) x

/-- Base change carries a product of degree-one generators to the product of their images. -/
private theorem mapₛₗ_prod_ι (φ : R →+* S) (u : M →ₛₗ[φ] N) {n : ℕ} (s : Fin n → M) :
    mapₛₗ φ u (∏ i : Fin n, SymmetricAlgebra.ι R M (s i)) =
      ∏ i : Fin n, SymmetricAlgebra.ι S N (u (s i)) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => mapₛₗ_ι φ u (s i)

/-- Base change carries the `n`-th symmetric power into the `n`-th symmetric power. -/
theorem mapₛₗ_mem_symmetricPower (φ : R →+* S) (u : M →ₛₗ[φ] N) (n : ℕ)
    {x : SymmetricAlgebra R M} (hx : x ∈ SymPow.symmetricPower n R M) :
    mapₛₗ φ u x ∈ SymPow.symmetricPower n S N := by
  rw [symmetricPower_eq_span_prod_ι] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      rw [mapₛₗ_prod_ι]
      exact prod_ι_mem S _
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul r y _ hy => simpa only [mapₛₗ_smul] using Submodule.smul_mem _ (φ r) hy


/-! ### Lifting into a ring with commuting image -/

section LiftComm

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {T : Type*} [Ring T] [Module R T]
  {h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y)}
  {h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y)}
  {γ : M →ₗ[R] T} {hγ : ∀ m m' : M, γ m * γ m' = γ m' * γ m}

open scoped IsMulCommutative in
/-- **Lifting out of the symmetric algebra into a ring with commuting image.** A linear map
`γ : M →ₗ[R] T` into a ring whose image consists of pairwise commuting elements extends to a
ring homomorphism `SymmetricAlgebra R M →+* T` which carries `ι R M m` to `γ m` and is linear
over `R`.

`SymmetricAlgebra.lift` requires the target to be a *commutative* `R`-algebra. The target here
is an arbitrary ring carrying a compatible `R`-module structure, and the construction factors
through the commutative subalgebra generated by the image of `γ`. This is what lets the graded
algebra of a sheaf of modules — whose sections do not commute across degrees — still receive
the symmetric algebra of its degree-one part.

The statement is existential so that the `Algebra R T` structure `r • 1`, which is not an
instance and is not canonical, stays inside the proof; `liftComm` below names the map. -/
@[ega "II 1.7.14" "partial"]
theorem exists_liftComm
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) (hγ : ∀ m m' : M, γ m * γ m' = γ m' * γ m) :
    ∃ Φ : SymmetricAlgebra R M →+* T,
      (∀ m : M, Φ (SymmetricAlgebra.ι R M m) = γ m) ∧
        ∀ (r : R) (x : SymmetricAlgebra R M), Φ (r • x) = r • Φ x := by
  let _ : Algebra R T := Algebra.ofModule h₁ h₂
  let _ := Algebra.isMulCommutative_adjoin R (s := Set.range γ)
    (by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ -; exact hγ m m')
  set f : M →ₗ[R] Algebra.adjoin R (Set.range γ) :=
    { toFun := fun m => ⟨γ m, Algebra.subset_adjoin ⟨m, rfl⟩⟩
      map_add' := fun m m' => Subtype.ext (map_add γ m m')
      map_smul' := fun r m => by exact Subtype.ext (map_smul γ r m) } with hf
  refine ⟨(Algebra.adjoin R (Set.range γ)).val.toRingHom.comp
    (SymmetricAlgebra.lift f).toRingHom, fun m => ?_, fun r x => ?_⟩
  · exact congrArg Subtype.val (SymmetricAlgebra.lift_ι_apply f m)
  · have hone : ((Algebra.adjoin R (Set.range γ)).val.toRingHom.comp
        (SymmetricAlgebra.lift f).toRingHom) (algebraMap R (SymmetricAlgebra R M) r) =
        r • (1 : T) := by
      show ((SymmetricAlgebra.lift f) (algebraMap R (SymmetricAlgebra R M) r) : T) = r • (1 : T)
      rw [AlgHom.commutes]
      show ((algebraMap R (Algebra.adjoin R (Set.range γ)) r : Algebra.adjoin R (Set.range γ)) :
        T) = r • (1 : T)
      rw [Subalgebra.coe_algebraMap]
      exact Algebra.algebraMap_eq_smul_one (A := T) r
    rw [Algebra.smul_def, map_mul, hone, h₁, one_mul]

/-- The ring homomorphism `SymmetricAlgebra R M →+* T` extending a linear map with pairwise
commuting image; see `SymmetricAlgebra.exists_liftComm`. -/
noncomputable def liftComm
    (h₁ : ∀ (r : R) (x y : T), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : T), x * r • y = r • (x * y))
    (γ : M →ₗ[R] T) (hγ : ∀ m m' : M, γ m * γ m' = γ m' * γ m) :
    SymmetricAlgebra R M →+* T :=
  (exists_liftComm h₁ h₂ γ hγ).choose

/-- `liftComm` sends the generator `ι R M m` to `γ m`. -/
@[simp]
theorem liftComm_ι (m : M) : liftComm h₁ h₂ γ hγ (SymmetricAlgebra.ι R M m) = γ m :=
  (exists_liftComm h₁ h₂ γ hγ).choose_spec.1 m

/-- `liftComm` commutes with scalar multiplication by `R`. -/
theorem liftComm_smul (r : R) (x : SymmetricAlgebra R M) :
    liftComm h₁ h₂ γ hγ (r • x) = r • liftComm h₁ h₂ γ hγ x :=
  (exists_liftComm h₁ h₂ γ hγ).choose_spec.2 r x

/-- The value of `liftComm` on a product of degree-one generators is the corresponding ordered
product in the target. With `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` this determines
`liftComm` on every symmetric power.

The product in the target is the ordered `List.prod`, not a `Finset.prod`: `T` is not assumed
commutative, only the image of `γ` is. -/
theorem liftComm_prod_ι {n : ℕ} (s : Fin n → M) :
    liftComm h₁ h₂ γ hγ (∏ i : Fin n, SymmetricAlgebra.ι R M (s i)) =
      (List.ofFn fun i => γ (s i)).prod := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, liftComm_ι]

end LiftComm

end BaseChange

end SymmetricAlgebra

namespace SymPow

/-- **Base change of the `n`-th symmetric power.** The restriction of
`SymmetricAlgebra.mapₛₗ φ u` to the degree-`n` pieces, as a `φ`-semilinear map
`Sym^n_R(M) →ₛₗ[φ] Sym^n_S(N)`. -/
noncomputable def symMapₛₗ {R S : Type*} [CommRing R] [CommRing S]
    {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]
    (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) :
    SymPow.symmetricPower n R M →ₛₗ[φ] SymPow.symmetricPower n S N where
  toFun x := ⟨SymmetricAlgebra.mapₛₗ φ u x,
    SymmetricAlgebra.mapₛₗ_mem_symmetricPower φ u n x.2⟩
  map_add' x y := Subtype.ext (map_add (SymmetricAlgebra.mapₛₗ φ u) x.1 y.1)
  map_smul' r x := Subtype.ext (SymmetricAlgebra.mapₛₗ_smul φ u r x)

/-- The underlying element of `symMapₛₗ n φ u x` in the symmetric algebra is
`SymmetricAlgebra.mapₛₗ φ u x`. -/
@[simp]
theorem symMapₛₗ_coe {R S : Type*} [CommRing R] [CommRing S]
    {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module S N]
    (n : ℕ) (φ : R →+* S) (u : M →ₛₗ[φ] N) (x : SymPow.symmetricPower n R M) :
    (symMapₛₗ n φ u x : SymmetricAlgebra S N) = SymmetricAlgebra.mapₛₗ φ u x := rfl

end SymPow

namespace PresheafOfModules

/-! ### The presheaf of sectionwise symmetric powers -/

section SymPowPresheaf

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The restriction map of the presheaf of sectionwise symmetric powers, as an additive map
whose target type is written as a symmetric power rather than as a restriction of scalars. -/
noncomputable def symPowRestrict (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+
      SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y) :=
  (SymPow.symMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)).toAddMonoidHom

/-- The underlying element of `symPowRestrict n F f x` in the symmetric algebra is the image
of `x` under `SymmetricAlgebra.mapₛₗ` along the restriction map of `F`. -/
@[simp]
theorem symPowRestrict_coe (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (symPowRestrict n F f x : SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise symmetric powers. -/
noncomputable def symPowAb (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    Cᵒᵖ ⥤ Ab.{max w a} where
  obj X := AddCommGrpCat.of
    (SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X))
  map f := AddCommGrpCat.ofHom (symPowRestrict n F f)
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact SymmetricAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g) (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

/-- The sections of `symPowAb n F` over `X` form a module over `O(X)`, namely the module
`Sym^n_{O(X)}(F(X))`. -/
noncomputable instance symPowAbModule (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((symPowAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)))

/-- **The presheaf of sectionwise symmetric powers.** Its sections over `X` are
`Sym^n_{O(X)}(F(X))`, the degree-`n` submodule of the symmetric algebra of `F(X)` over `O(X)`,
and its restriction maps are the symmetric powers of the restriction maps of `F`, in the
semilinear sense of `SymPow.symMapₛₗ`. -/
noncomputable def symPow (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (symPowAb n F) fun {_ _} _ r _ => Subtype.ext
    (SymmetricAlgebra.mapₛₗ_smul _ _ r _)

/-- **The sectionwise identification.** The sections of `symPow n F` over `X` are the `n`-th
symmetric power of the sections of `F` over `X`. The equivalence is the identity: the presheaf
is defined sectionwise, and this records the identification in the form a consumer needs. -/
noncomputable def symPowSections (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    (symPow n F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
  LinearEquiv.refl _ _

/-- The restriction maps of `symPow n F` are the symmetric powers of the restriction maps of
`F`, read through the sectionwise identification. -/
theorem symPowSections_map (n : ℕ) (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (symPow n F).obj X) :
    (symPowSections n F Y ((symPow n F).map f x) :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      SymmetricAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
        (symPowSections n F X x) := rfl

/-- **The restriction maps of `symPow n F` on products of degree-one generators.** If a section
of `symPow n F` over `X` is the product of the generators `s i`, its restriction to `Y` is the
product of the generators `F.map f (s i)`. Since those products span (`SymPow.ext_of_prod_ι`),
this determines the restriction maps. -/
theorem symPowSections_map_prod_ι (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : Fin n → F.obj X) (x : (symPow n F).obj X)
    (hx : (symPowSections n F X x :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)) :
    (symPowSections n F Y ((symPow n F).map f x) :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)
        (F.map f (s i)) := by
  rw [symPowSections_map, hx]
  exact SymmetricAlgebra.mapₛₗ_prod_ι _ _ s

end SymPowPresheaf

end PresheafOfModules

namespace SymPow

/-- Two semilinear maps out of the `n`-th symmetric power which agree on the products of `n`
degree-one generators are equal: those products span the symmetric power, by
`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`. -/
theorem ext_of_prod_ι {R S : Type*} [CommRing R] [CommRing S] {M : Type*} [AddCommGroup M]
    [Module R M] {N : Type*} [AddCommGroup N] [Module S N] {φ : R →+* S} {n : ℕ}
    {f g : SymPow.symmetricPower n R M →ₛₗ[φ] N}
    (h : ∀ s : Fin n → M,
      f ⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ =
        g ⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩) :
    f = g := by
  refine LinearMap.ext_on_range (v := fun s : Fin n → M =>
    (⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
      SymPow.symmetricPower n R M)) ?_ h
  refine eq_top_iff.2 fun x _ => ?_
  have himg : (x : SymmetricAlgebra R M) ∈
      Submodule.map (SymPow.symmetricPower n R M).subtype
        (Submodule.span R (Set.range fun s : Fin n → M =>
          (⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
            SymPow.symmetricPower n R M))) := by
    rw [Submodule.map_span, ← Set.range_comp,
      show ((SymPow.symmetricPower n R M).subtype ∘ fun s : Fin n → M =>
          (⟨∏ i : Fin n, SymmetricAlgebra.ι R M (s i), SymmetricAlgebra.prod_ι_mem R s⟩ :
            SymPow.symmetricPower n R M)) =
          fun s : Fin n → M => ∏ i : Fin n, SymmetricAlgebra.ι R M (s i) from rfl,
      ← SymmetricAlgebra.symmetricPower_eq_span_prod_ι]
    exact x.2
  obtain ⟨z, hz, hzx⟩ := himg
  exact Subtype.ext hzx ▸ hz

end SymPow

namespace Stacks.GradedAlgebra

/-! ### The comparison with the degree-`n` piece of a graded algebra -/

section Comparison

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (gen : F ⟶ Pc 1)

/-- The degree-one local sections in the image of a generator `F ⟶ Pc 1` commute pairwise. This
is the presheaf-level form of `SheafOfModules.GradedAlgebra.PairwiseCommutes`. -/
def GenCommutes : Prop :=
  ∀ (X : Cᵒᵖ) (x y : F.obj X),
    (A.mul 1 1).app X (gen.app X x) (gen.app X y) =
      (A.mul 1 1).app X (gen.app X y) (gen.app X x)

/-- A local section of `F`, viewed in degree one of the ungraded realization of the graded
algebra. -/
noncomputable def genLin (X : Cᵒᵖ) :
    F.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] A.Total X where
  toFun m := A.incl 1 (gen.app X m)
  map_add' m m' := by rw [map_add, A.incl_add]
  map_smul' r m := by rw [RingHom.id_apply, map_smul, A.incl_smul]

/-- `genLin gen X m` is the degree-one element `incl 1 (gen.app X m)`. -/
@[simp]
theorem genLin_apply (X : Cᵒᵖ) (m : F.obj X) : A.genLin gen X m = A.incl 1 (gen.app X m) := rfl

/-- The images of any two sections under `genLin gen X` commute. -/
theorem genLin_mul_comm (hc : A.GenCommutes gen) (X : Cᵒᵖ) (m m' : F.obj X) :
    A.genLin gen X m * A.genLin gen X m' = A.genLin gen X m' * A.genLin gen X m := by
  rw [genLin_apply, genLin_apply, A.incl_mul_incl, A.incl_mul_incl, hc X m m']

/-- The ring homomorphism from the symmetric algebra of the sections of `F` over `X` to the
ungraded realization of the graded algebra over `X`, determined by the degree-one generator. -/
noncomputable def liftTotal (hc : A.GenCommutes gen) (X : Cᵒᵖ) :
    SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →+* A.Total X :=
  SymmetricAlgebra.liftComm (fun r x y => A.smul_mul_eq (X := X) r x y)
    (fun r x y => A.mul_smul_eq (X := X) r x y) (A.genLin gen X) (A.genLin_mul_comm gen hc X)

/-- The projection of the ungraded realization onto its degree-`i` component. -/
noncomputable def proj (X : Cᵒᵖ) (i : ℤ) :
    A.Total X →ₗ[(O ⋙ forget₂ _ RingCat).obj X] (Pc i).obj X :=
  DirectSum.component _ ℤ (fun j => ((Pc j).obj X : Type (max w a))) i

/-- Projecting the degree-`i` inclusion of `x` onto the degree-`i` component returns `x`. -/
@[simp]
theorem proj_incl (X : Cᵒᵖ) (i : ℤ) (x : (Pc i).obj X) : A.proj X i (A.incl i x) = x := by
  show DirectSum.component _ ℤ (fun j => ((Pc j).obj X : Type (max w a))) i
    (DirectSum.of (fun j => ((Pc j).obj X : Type (max w a))) i x) = x
  rw [← DirectSum.lof_eq_of ((O ⋙ forget₂ _ RingCat).obj X)]
  exact DirectSum.component.lof_self (M := fun j => ((Pc j).obj X : Type (max w a)))
    ((O ⋙ forget₂ _ RingCat).obj X) i x

/-- The ordered product of `n` degree-one local sections of a graded algebra, as a homogeneous
section of degree `n`. The empty product is the algebra unit.

The recursion multiplies on the right, so the degree of the result is `(n : ℤ) + 1`, which is
*definitionally* `((n + 1 : ℕ) : ℤ)`. Multiplying on the left would give `1 + (n : ℤ)` and force
a transport along `Int.add_comm` into every statement about the product. -/
noncomputable def homogeneousProd (X : Cᵒᵖ) :
    (n : ℕ) → (Fin n → (Pc 1).obj X) → (Pc (n : ℤ)).obj X
  | 0, _ => A.one.eval X
  | n + 1, z =>
      (A.mul (n : ℤ) 1).app X (homogeneousProd X n fun i => z i.castSucc) (z (Fin.last n))

/-- The ordered product of degree-one sections, read in the ungraded realization, is the product
of their images. This characterizes `homogeneousProd`, since `Stacks.GradedAlgebra.incl` is
injective. -/
theorem incl_homogeneousProd (X : Cᵒᵖ) (n : ℕ) (z : Fin n → (Pc 1).obj X) :
    A.incl (n : ℤ) (A.homogeneousProd X n z) = (List.ofFn fun i => A.incl 1 (z i)).prod := by
  induction n with
  | zero =>
      rw [List.ofFn_zero, List.prod_nil]
      exact (A.one_eq_incl X).symm
  | succ n ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
        ← ih fun i => z i.castSucc]
      exact (A.incl_mul_incl (n : ℤ) 1 (A.homogeneousProd X n fun i => z i.castSucc)
        (z (Fin.last n))).symm

/-- The ordered product of degree-one sections commutes with restriction. -/
theorem homogeneousProd_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℕ) (z : Fin n → (Pc 1).obj X) :
    (Pc (n : ℤ)).map f (A.homogeneousProd X n z) =
      A.homogeneousProd Y n fun i => (Pc 1).map f (z i) := by
  induction n with
  | zero => exact PresheafOfModules.sections_property A.one f
  | succ n ih =>
      show (Pc ((n : ℤ) + 1)).map f ((A.mul (n : ℤ) 1).app X _ _) = _
      rw [(A.mul (n : ℤ) 1).naturality f, ih fun i => z i.castSucc]
      rfl

/-- **The comparison map on sections.** The `n`-th symmetric power of the sections of `F` over
`X` maps to the degree-`n` sections of the graded algebra, by multiplying out the generators. -/
noncomputable def cmpSections (hc : A.GenCommutes gen) (n : ℕ) (X : Cᵒᵖ) :
    SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →ₗ[(O ⋙ forget₂ _
      RingCat).obj X] (Pc (n : ℤ)).obj X :=
  (A.proj X (n : ℤ)).comp
    (({ toFun := fun x => A.liftTotal gen hc X x
        map_add' := fun x y => map_add (A.liftTotal gen hc X) x y
        map_smul' := fun r x => SymmetricAlgebra.liftComm_smul r x } :
          SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →ₗ[(O ⋙ forget₂ _
            RingCat).obj X] A.Total X).comp
      (SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)).subtype)

/-- `cmpSections gen hc n X x` is the degree-`n` component of `liftTotal gen hc X x`. -/
theorem cmpSections_apply (hc : A.GenCommutes gen) (n : ℕ) (X : Cᵒᵖ)
    (x : SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    A.cmpSections gen hc n X x = A.proj X (n : ℤ) (A.liftTotal gen hc X x) := rfl

/-- **The comparison map on products of generators.** This is the equation that Tag 01CG states
the comparison by, and by `SymPow.ext_of_prod_ι` it determines the map. -/
theorem cmpSections_prod_ι (hc : A.GenCommutes gen) (n : ℕ) (X : Cᵒᵖ) (s : Fin n → F.obj X) :
    A.cmpSections gen hc n X
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i),
          SymmetricAlgebra.prod_ι_mem _ s⟩ =
      A.homogeneousProd X n fun i => gen.app X (s i) := by
  rw [cmpSections_apply]
  show A.proj X (n : ℤ) (A.liftTotal gen hc X
    (∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i))) = _
  rw [liftTotal, SymmetricAlgebra.liftComm_prod_ι]
  show A.proj X (n : ℤ) (List.ofFn fun i => A.incl 1 (gen.app X (s i))).prod = _
  rw [← A.incl_homogeneousProd X n fun i => gen.app X (s i), A.proj_incl]

/-- The comparison map on sections commutes with restriction. -/
theorem cmpSections_naturality (hc : A.GenCommutes gen) (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (Pc (n : ℤ)).map f (A.cmpSections gen hc n X x) =
      A.cmpSections gen hc n Y
        (SymPow.symMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) := by
  have key : ((Pc (n : ℤ)).restrictₛₗ f).comp (A.cmpSections gen hc n X) =
      (A.cmpSections gen hc n Y).comp
        (SymPow.symMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)) := by
    refine SymPow.ext_of_prod_ι fun s => ?_
    have himg : SymPow.symMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f)
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i),
            SymmetricAlgebra.prod_ι_mem _ s⟩ =
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj Y) (F.obj Y)
            (F.restrictₛₗ f (s i)), SymmetricAlgebra.prod_ι_mem _ _⟩ := by
      exact Subtype.ext (SymmetricAlgebra.mapₛₗ_prod_ι _ _ s)
    show (Pc (n : ℤ)).map f (A.cmpSections gen hc n X _) =
      A.cmpSections gen hc n Y (SymPow.symMapₛₗ n _ (F.restrictₛₗ f) _)
    rw [cmpSections_prod_ι, A.homogeneousProd_naturality f n, himg, cmpSections_prod_ι]
    exact congrArg (A.homogeneousProd Y n)
      (funext fun i => (PresheafOfModules.naturality_apply gen f (s i)).symm)
  exact DFunLike.congr_fun key x

/-- **The comparison morphism.** The presheaf of sectionwise `n`-th symmetric powers of `F` maps
to the degree-`n` piece of a graded algebra carrying a pairwise-commuting degree-one generator
`F ⟶ Pc 1`, by multiplying out the generators. -/
noncomputable def cmp (hc : A.GenCommutes gen) (n : ℕ) :
    PresheafOfModules.symPow n F ⟶ Pc (n : ℤ) where
  app X := ModuleCat.ofHom (A.cmpSections gen hc n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (A.cmpSections_naturality gen hc n f x).symm)

/-- The component of `cmp gen hc n` over `X` is `cmpSections gen hc n X`. -/
@[simp]
theorem cmp_app (hc : A.GenCommutes gen) (n : ℕ) (X : Cᵒᵖ)
    (x : (PresheafOfModules.symPow n F).obj X) :
    (A.cmp gen hc n).app X x = A.cmpSections gen hc n X
      (PresheafOfModules.symPowSections n F X x) := rfl

end Comparison

end Stacks.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

/-! ### The comparison for a sheaf of graded algebras -/

section Sheaf

/-- The sheaf of rings underlying a presheaf of commutative rings which happens to be a sheaf.
Writing the base this way, rather than as `sheafCompose J (forget₂ CommRingCat RingCat)`, keeps
the underlying presheaf of rings *syntactically* `O ⋙ forget₂ CommRingCat RingCat`, which is
what the sectionwise symmetric powers are built over. -/
abbrev ringSheafOfIsSheaf {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (hO : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat RingCat)) : Sheaf J RingCat.{w} :=
  ⟨O ⋙ forget₂ CommRingCat RingCat, hO⟩

/-- `ringSheafOfIsSheaf` agrees on the nose with `CategoryTheory.Sheaf.toRingCat`: the two are
the same term once the sheaf condition is taken to be the one `toRingCat` supplies. In
particular `structureSheafRing X` is
`toRingCat _ X.sheaf`, hence `ringSheafOfIsSheaf` at that proof.

`toRingCat` is *not* used in its place below, because it demands a sheaf of commutative rings
together with `J.HasSheafCompose (forget₂ CommRingCat RingCat)`, whereas everything here needs
only that the underlying presheaf of rings is a sheaf. Substituting it would strengthen the
hypotheses of every statement in this section. -/
theorem ringSheafOfIsSheaf_eq_toRingCat {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (Osharp : Sheaf J CommRingCat.{w}) :
    ringSheafOfIsSheaf (O := Osharp.obj) (CategoryTheory.Sheaf.toRingCat J Osharp).property =
      CategoryTheory.Sheaf.toRingCat J Osharp := rfl

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat RingCat)}
  {M : SheafOfModules.{max w a} (ringSheafOfIsSheaf hO)}
  (A : SheafOfModules.GradedAlgebra.{w, max w a} (ringSheafOfIsSheaf hO)) (gen : M ⟶ A.piece 1)

/-- **The comparison morphism for a sheaf of graded algebras.** The presheaf of sectionwise
`n`-th symmetric powers of `M` maps to the degree-`n` piece of a sheaf of graded algebras
carrying a pairwise-commuting degree-one generator `M ⟶ A.piece 1`.

This is `Stacks.GradedAlgebra.cmp` read through
`SheafOfModules.GradedAlgebra.toPresheafGradedAlgebra`: a sheaf of graded algebras is in
particular a graded algebra of presheaves of modules, and the comparison does not see the sheaf
conditions. -/
noncomputable def symPowCmp (hgen : SheafOfModules.GradedAlgebra.PairwiseCommutes gen) (n : ℕ) :
    PresheafOfModules.symPow n M.val ⟶ (A.piece (n : ℤ)).val :=
  A.toPresheafGradedAlgebra.cmp gen.val (fun X x y => hgen X x y) n

/-- The comparison morphism of `symPowCmp` sends the product of `n` degree-one generators to
their ordered product in the graded algebra, read in the ungraded realization. By
`SymPow.ext_of_prod_ι` this determines the morphism. -/
theorem incl_symPowCmp_prod_ι (hgen : SheafOfModules.GradedAlgebra.PairwiseCommutes gen) (n : ℕ)
    (X : Cᵒᵖ) (s : Fin n → M.val.obj X) (x : (PresheafOfModules.symPow n M.val).obj X)
    (hx : (PresheafOfModules.symPowSections n M.val X x :
        SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (M.val.obj X)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (M.val.obj X) (s i)) :
    A.toPresheafGradedAlgebra.incl (n : ℤ) ((A.symPowCmp gen hgen n).app X x) =
      (List.ofFn fun i => A.toPresheafGradedAlgebra.incl 1 (gen.val.app X (s i))).prod := by
  have hxeq : x = ⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X)
      (M.val.obj X) (s i), SymmetricAlgebra.prod_ι_mem _ s⟩ := Subtype.ext hx
  rw [hxeq]
  refine Eq.trans (congrArg (A.toPresheafGradedAlgebra.incl (n : ℤ))
    (Stacks.GradedAlgebra.cmpSections_prod_ι A.toPresheafGradedAlgebra gen.val
      (fun X x y => hgen X x y) n X s)) ?_
  exact Stacks.GradedAlgebra.incl_homogeneousProd A.toPresheafGradedAlgebra X n _

end Sheaf

end SheafOfModules.GradedAlgebra
