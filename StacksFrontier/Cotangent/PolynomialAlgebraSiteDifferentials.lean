module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteAugmentationIdeal
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials on the site of a polynomial algebra

Let `A → B` be a ring map and work on the site `C_{B/A}` of polynomial `A`-algebras augmented
to `B`, as in `StacksFrontier/Cotangent/PolynomialAlgebraSite.lean`. Beside the structure sheaf
`𝒪`, which sends `(P, α)` to `P`, the site carries the constant sheaf of rings with value `A`,
and the `A`-algebra structures of the objects assemble into a map of sheaves of rings
`A̲ → 𝒪`. This file forms the sheaf of relative differentials

```
Ω_{𝒪/A} = Ω_{𝒪/A̲},
```

a sheaf of `𝒪`-modules whose sections over `(P, α)` are `Ω[P⁄A]`, and its base change

```
Ω₁ = B̲ ⊗_𝒪 Ω_{𝒪/A},
```

a sheaf of `B̲`-modules whose sections over `(P, α)` are `B ⊗_P Ω[P⁄A]`. The latter is the
sheaf whose derived lower shriek the source computes to be the cotangent complex `L_{B/A}`.
Finally `Ω_{𝒪/A}` is flat over `𝒪`, because each of its values `Ω[P⁄A]` is a free `P`-module:
`P` is a polynomial algebra over `A`, so `Ω[P⁄A]` is free on the variables.

Because the topology of `C_{B/A}` is chaotic, every presheaf on the site is a sheaf, and all
three constructions are taken objectwise: no sheafification is involved, and the sections are
read off definitionally. In particular `Ω_{𝒪/A}` is *defined* to be Mathlib's presheaf of
relative differentials of `A̲ → 𝒪`, and the fact that this is the sheaf of differentials of
Tag 04BL — that it corepresents the functor of relative derivations on sheaves of
`𝒪`-modules — is proved rather than built in.

## Main definitions

* `CommAlgCat.polynomialBaseSheaf`: the constant sheaf of rings `A̲` on `C_{B/A}`, and
  `CommAlgCat.polynomialBaseStructureHom`: the map of sheaves of rings `A̲ ⟶ 𝒪` given by the
  `A`-algebra structures.
* `CommAlgCat.polynomialRelativeDifferentials`: the sheaf of `𝒪`-modules `Ω_{𝒪/A}`.
* `CommAlgCat.polynomialRelativeDifferentialsBaseChange`: the sheaf of `B̲`-modules
  `Ω₁ = B̲ ⊗_𝒪 Ω_{𝒪/A}`.
* `KaehlerDifferential.uliftLinearEquiv`: the universe lift of a module of Kähler
  differentials, namely `Ω[(ULift P)⁄(ULift A)] ≃ Ω[P⁄A]`, which is what turns the sections of
  `Ω_{𝒪/A}` into Kähler differentials of the algebras themselves.

## Main results

* `CommAlgCat.polynomialRelativeDifferentials_obj` and
  `CommAlgCat.polynomialRelativeDifferentialsSectionsEquiv`: the sections of `Ω_{𝒪/A}` over
  `(P, α)` are `Ω[P⁄A]`.
* `CommAlgCat.polynomialRelativeDifferentialsCorepresentableBy`: `Ω_{𝒪/A}` corepresents the
  functor of relative derivations of `𝒪` over `A̲` with values in a sheaf of `𝒪`-modules, so
  it is the sheaf of differentials in the sense of Tag 04BL.
* `CommAlgCat.polynomialRelativeDifferentialsBaseChange_obj`: the sections of `Ω₁` over
  `(P, α)` are `B̲(P, α) ⊗_P Ω_{𝒪/A}(P, α)`, which is `B ⊗_P Ω[P⁄A]` once the two factors are
  identified by `CommAlgCat.polynomialConstantSheafIso` and
  `CommAlgCat.polynomialRelativeDifferentialsSectionsEquiv`.
* `CommAlgCat.polynomialRelativeDifferentials_isFlat`: `Ω_{𝒪/A}` is a flat sheaf of
  `𝒪`-modules.
* `CommAlgCat.free_kaehlerDifferential_of_isPolynomialAlgebra`: the module of differentials of
  a polynomial algebra is free, which is the objectwise input to flatness.

## Implementation notes

**Universes and the universe lift.** Tag 08PF forms the morphism of topoi `π` on sheaves
valued in a universe containing the site, so the two sheaves of rings of `C_{B/A}` take their
values in `CommRingCat.{u + 1}` when `A` and `B` live in `Type u`, and the structure sheaf is
built with `CommAlgCat.uliftFunctor`. Its value over `(P, α)` is therefore `ULift P`, and the
constant sheaf of rings `A̲` has to be the constant presheaf with value `ULift A`, exactly as
`CommAlgCat.polynomialConstantPresheaf` has value `ULift B`. Consequently the sections of
`Ω_{𝒪/A}` over `(P, α)` are `Ω[(ULift P)⁄(ULift A)]` on the nose, and the identification with
`Ω[P⁄A]` is the content of `KaehlerDifferential.uliftLinearEquiv`. That isomorphism is
canonical, not basis-dependent: the map down is the universal property of
`Ω[(ULift P)⁄(ULift A)]` applied to the derivation `x ↦ d x.down`, the map up is
`KaehlerDifferential.map` for the square `A → ULift A`, `P → ULift P`, and the two round trips
are checked on the differentials `d x`, which generate.

**Instances versus ring maps.** `CommRingCat.KaehlerDifferential f` installs the algebra
structure `f.hom.toAlgebra`, whose scalar multiplication is `r • x = f r * x`, whereas the
algebra structure that instance resolution produces for `ULift A` acting on `ULift P` is
`ULift.algebra'`. The two have the same `algebraMap` but are not definitionally equal, so the
statements about universe-lifted differentials are phrased for the instance coming from the
ring map — which is the one the sections of `Ω_{𝒪/A}` actually carry — and the proofs transport
along `Algebra.algebra_ext` to the instance under which the `ULift` lemmas of Mathlib apply.

**Flatness.** The library's flatness predicate for a sheaf of modules on a site is
`AlgebraicGeometry.SheafOfModules.IsFlat` (Tag 03ER), exactness of tensoring with it, and the
available criterion is Tag 0GN1, `isFlat_sheafification_of_locally_objectwise_flat`: the
sheafification of an objectwise flat presheaf of modules is flat. It is applied along the
identity comparison map `polynomialRingUnit`, for the covering of an object by its own
identity, and its conclusion is transported from the sheafification of `Ω_{𝒪/A}` to
`Ω_{𝒪/A}` itself by `isFlat_of_retract`: the unit of the sheafification adjunction and the
morphism that the adjunction attaches to the identity exhibit `Ω_{𝒪/A}` as a retract of its
sheafification, with no need to know that the unit is an isomorphism.

**Spelling of the ring sheaf.** `CommAlgCat.polynomialStructureRingSheaf`,
`Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.SheafOfModules.Tensor.ringSheaf` all unfold to
`(sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪`, so they agree definitionally; but the
first one reaches it through the ringed topos of Tag 08PR, which is a plain `def` and
therefore does not unfold at reducible transparency, and `Presheaf.IsLocallyInjective` is found
by keyed instance matching. The comparison map along which presheaves of modules are sheafified
is therefore declared twice, once at each of the first two spellings, with the same two
instances on each: the public statements use the spelling of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteAugmentationIdeal.lean` and Tag 0GN1 is applied at
its own.

**What this file does not do.** It proves none of the statements of Tag 08QU or of the remaining
clauses of 08R7, which compute `Lπ_!` of the sheaves built here. Two of the tags the source also
deduces from `Lπ_!` are available elsewhere: Tag 08QW, the identities `Lg_{i,!} ∘ g_i⁻¹ = id` and
`Lπ_! ∘ g_i⁻¹ = Lπ_{i,!}` that those computations use, is
`CommAlgCat.derivedLowerShriek_comp_inverseImage_polynomialTower` in
`StacksFrontier/Cotangent/ThreefoldLowerShriekComparison.lean`; and Tag 08QX is proved by a different
route, as `CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean` — Remark 08SD's split injection followed by
flat base change, which needs no `Lπ_!` at all. What is provided here is their input: the sheaf
`Ω₁`, its sections, and the flatness of `Ω_{𝒪/A}` that lets `Li^*` be replaced by `i^*` in the
argument of Tag 08PU.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v

/-! ### Universe lifts of Kähler differentials -/

namespace KaehlerDifferential

variable (A : Type u) [CommRing A] (P : Type u) [CommRing P] [Algebra A P]

/-- The structure map `ULift A → ULift P` of the universe lift of an `A`-algebra `P`, as a ring
map. This is the ring map whose module of Kähler differentials appears as a module of sections
of the sheaf of differentials on `CommAlgCat.polynomialSite`. -/
abbrev uliftAlgebraMap : ULift.{v} A →+* ULift.{v} P :=
  RingHom.comp (algebraMap A (ULift.{v} P)) (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom

section Lift

attribute [local instance] ULift.algebra'

/-- The derivation of `ULift P` over `ULift A` with values in `Ω[P⁄A]` that sends a section `x`
to `d x.down`. -/
def uliftDerivation : Derivation (ULift.{v} A) (ULift.{v} P) Ω[P⁄A] where
  toFun x := KaehlerDifferential.D A P x.down
  map_add' x y := by simp
  map_smul' a x := (KaehlerDifferential.D A P).map_smul a.down x.down
  map_one_eq_zero' := by simp
  leibniz' a b := (KaehlerDifferential.D A P).leibniz a.down b.down

/-- The comparison map `Ω[(ULift P)⁄(ULift A)] → Ω[P⁄A]`, which sends `d x` to `d x.down`. -/
def uliftDown : Ω[ULift.{v} P⁄ULift.{v} A] →ₗ[ULift.{v} P] Ω[P⁄A] :=
  (uliftDerivation.{u, v} A P).liftKaehlerDifferential

/-- The comparison map `Ω[P⁄A] → Ω[(ULift P)⁄(ULift A)]`, which sends `d p` to `d (up p)`. It is
`KaehlerDifferential.map` for the square of ring maps `A → ULift A`, `P → ULift P`. -/
def uliftUp : Ω[P⁄A] →ₗ[P] Ω[ULift.{v} P⁄ULift.{v} A] :=
  KaehlerDifferential.map A (ULift.{v} A) P (ULift.{v} P)

/-- The map `KaehlerDifferential.uliftDown` sends `d (up p)` to `d p`. -/
@[simp]
lemma uliftDown_d (p : P) :
    uliftDown.{u, v} A P (KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) (ULift.up p)) =
      KaehlerDifferential.D A P p :=
  Derivation.liftKaehlerDifferential_comp_D _ _

/-- The map `KaehlerDifferential.uliftUp` sends `d p` to `d (up p)`. -/
@[simp]
lemma uliftUp_d (p : P) :
    uliftUp.{u, v} A P (KaehlerDifferential.D A P p) =
      KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) (ULift.up p) := by
  rw [uliftUp, KaehlerDifferential.map_D]
  rfl

/-- `KaehlerDifferential.uliftDown` is linear over `P`, not merely over `ULift P`. -/
def uliftDownRestrict : Ω[ULift.{v} P⁄ULift.{v} A] →ₗ[P] Ω[P⁄A] where
  toFun := uliftDown.{u, v} A P
  map_add' := map_add _
  map_smul' p y := by
    rw [show p • y = (ULift.up.{v} p) • y from
      (IsScalarTower.algebraMap_smul (ULift.{v} P) p y).symm, map_smul]
    rfl

/-- `KaehlerDifferential.uliftUp` is linear over `ULift P`, not merely over `P`. -/
def uliftUpExtend : Ω[P⁄A] →ₗ[ULift.{v} P] Ω[ULift.{v} P⁄ULift.{v} A] where
  toFun := uliftUp.{u, v} A P
  map_add' := map_add _
  map_smul' q y := by
    change uliftUp.{u, v} A P (q.down • y) = q • uliftUp.{u, v} A P y
    rw [map_smul, show (q.down : P) • uliftUp.{u, v} A P y =
      (ULift.up.{v} q.down) • uliftUp.{u, v} A P y from
        (IsScalarTower.algebraMap_smul (ULift.{v} P) q.down _).symm]

/-- The map `KaehlerDifferential.uliftDown` is a left inverse of `KaehlerDifferential.uliftUp`. -/
lemma uliftDown_uliftUp (w : Ω[P⁄A]) :
    uliftDown.{u, v} A P (uliftUp.{u, v} A P w) = w := by
  have h : (uliftDownRestrict.{u, v} A P).comp (uliftUp.{u, v} A P) = LinearMap.id := by
    ext p
    show uliftDown.{u, v} A P (uliftUp.{u, v} A P (KaehlerDifferential.D A P p)) =
      KaehlerDifferential.D A P p
    rw [uliftUp_d, uliftDown_d]
  exact LinearMap.congr_fun h w

/-- The map `KaehlerDifferential.uliftUp` is a left inverse of `KaehlerDifferential.uliftDown`. -/
lemma uliftUp_uliftDown (y : Ω[ULift.{v} P⁄ULift.{v} A]) :
    uliftUp.{u, v} A P (uliftDown.{u, v} A P y) = y := by
  have h : (uliftUpExtend.{u, v} A P).comp (uliftDown.{u, v} A P) = LinearMap.id := by
    ext q
    show uliftUp.{u, v} A P (uliftDown.{u, v} A P
        (KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) q)) =
      KaehlerDifferential.D (ULift.{v} A) (ULift.{v} P) q
    rw [show q = ULift.up.{v} q.down from rfl, uliftDown_d, uliftUp_d]
  exact LinearMap.congr_fun h y

/-- **The universe lift of Kähler differentials, for the algebra structure produced by instance
resolution.** The differentials of the universe lift `ULift P` over `ULift A` are the
differentials of `P` over `A`, by the map sending `d x` to `d x.down`. -/
def uliftLinearEquivOfInstance :
    Ω[ULift.{v} P⁄ULift.{v} A] ≃ₗ[ULift.{v} P] Ω[P⁄A] :=
  { uliftDown.{u, v} A P with
    invFun := uliftUp.{u, v} A P
    left_inv := uliftUp_uliftDown.{u, v} A P
    right_inv := uliftDown_uliftUp.{u, v} A P }

end Lift

/-- The algebra structure that the ring map `KaehlerDifferential.uliftAlgebraMap` induces agrees
with the one instance resolution finds: both have `algebraMap a = up (algebraMap a.down)`. -/
lemma uliftAlgebraMap_toAlgebra_eq :
    (uliftAlgebraMap.{u, v} A P).toAlgebra = ULift.algebra' A (ULift.{v} P) :=
  Algebra.algebra_ext _ _ (fun _ => rfl)

/-- **The universe lift of Kähler differentials.** For the algebra structure on `ULift P` over
`ULift A` coming from the lifted structure map, the differentials of `ULift P` over `ULift A`
are canonically the differentials of `P` over `A`. This is the identification under which the
sections of the sheaf of differentials on `CommAlgCat.polynomialSite` over the object `(P, α)`
become `Ω[P⁄A]`. -/
def uliftLinearEquiv :
    letI : Algebra (ULift.{v} A) (ULift.{v} P) := (uliftAlgebraMap.{u, v} A P).toAlgebra
    Ω[ULift.{v} P⁄ULift.{v} A] ≃ₗ[ULift.{v} P] Ω[P⁄A] := by
  rw [uliftAlgebraMap_toAlgebra_eq.{u, v} A P]
  exact uliftLinearEquivOfInstance.{u, v} A P

/-- **The universe lift of Kähler differentials is flat when the differentials are free.** This
is the objectwise input to the flatness of the sheaf of differentials on
`CommAlgCat.polynomialSite`: the value over `(P, α)` is flat over the value `ULift P` of the
structure sheaf. -/
lemma flat_ulift_of_free (hfree : Module.Free P Ω[P⁄A]) :
    letI : Algebra (ULift.{v} A) (ULift.{v} P) := (uliftAlgebraMap.{u, v} A P).toAlgebra
    Module.Flat (ULift.{v} P) Ω[ULift.{v} P⁄ULift.{v} A] := by
  rw [uliftAlgebraMap_toAlgebra_eq.{u, v} A P]
  have := hfree
  have : Module.Flat P Ω[P⁄A] := Module.Flat.of_free
  have : Module.Flat (ULift.{v} P) Ω[P⁄A] := Module.Flat.ulift_left_iff.2 inferInstance
  exact Module.Flat.of_linearEquiv (uliftLinearEquivOfInstance.{u, v} A P)

end KaehlerDifferential

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The constant sheaf of rings `A` and the map `A ⟶ 𝒪` -/

/-- Every presheaf on `C_{B/A}` is a sheaf, because the topology of the site is chaotic. -/
theorem isSheaf_polynomialTopology {D : Type*} [Category D]
    (F : (polynomialSite A B)ᵒᵖ ⥤ D) : Presheaf.IsSheaf (polynomialTopology A B) F := by
  rw [show polynomialTopology A B = ⊥ from polynomialTopology_eq_bot A B]
  exact Presheaf.isSheaf_bot _

/-- The objects of `C_{B/A}`, read as `A`-algebras with sections in the universe in which the
sheaves of rings of the site take their values. Composing with the forgetful functor to
commutative rings gives `CommAlgCat.polynomialStructurePresheaf`. -/
abbrev polynomialAlgebraFunctor : (polynomialSite A B)ᵒᵖ ⥤ CommAlgCat.{u + 1} A :=
  unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι ⋙
    Over.forget B ⋙ CommAlgCat.uliftFunctor.{u + 1, u} A

/-- The constant presheaf of rings with value `A` on `C_{B/A}`, with its sections in the
universe in which the morphism of topoi `π` of Tag 08PF is formed. -/
abbrev polynomialBasePresheaf : (polynomialSite A B)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Functor.const (polynomialSite A B)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))

/-- The `A`-algebra structures of the objects of `C_{B/A}`, as a map from the constant presheaf
with value `A` to the tautological presheaf of rings. -/
def polynomialBaseStructurePresheafHom :
    polynomialBasePresheaf A B ⟶ polynomialStructurePresheaf A B where
  app W := CommRingCat.ofHom
    (RingHom.comp (algebraMap A ((polynomialAlgebraFunctor A B).obj W))
      (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom)
  naturality _ _ f := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact (((polynomialAlgebraFunctor A B).map f).hom.commutes a.down).symm

/-- The constant sheaf of rings `A̲` on `C_{B/A}`. It is a sheaf because the topology of
`C_{B/A}` is chaotic. -/
def polynomialBaseSheaf : Sheaf (polynomialTopology A B) CommRingCat.{u + 1} :=
  ⟨polynomialBasePresheaf A B, isSheaf_polynomialTopology A B _⟩

/-- The map of sheaves of rings `A̲ ⟶ 𝒪` on `C_{B/A}` given by the `A`-algebra structures of
the objects of the site. -/
def polynomialBaseStructureHom : polynomialBaseSheaf A B ⟶ polynomialStructureSheaf A B :=
  ⟨polynomialBaseStructurePresheafHom A B⟩

/-- On sections over the object `(P, α)` of `C_{B/A}`, the map `A̲ ⟶ 𝒪` is the universe lift of
the structure map `A → P`. -/
theorem polynomialBaseStructureHom_app (X : polynomialSite A B) :
    (polynomialBaseStructureHom A B).hom.app (op X) =
      CommRingCat.ofHom (KaehlerDifferential.uliftAlgebraMap.{u, u + 1} A
        (X.unop.obj.left : Type u)) :=
  rfl

/-! ### The sheaf of relative differentials -/

/-- The presheaf of relative differentials of `A̲ ⟶ 𝒪`, whose value over `(P, α)` is the module
of Kähler differentials of the universe lift of `A → P`. -/
def polynomialRelativeDifferentialsPresheaf :
    PresheafOfModules.{u + 1} (polynomialStructureRingSheaf A B).obj :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (polynomialBaseStructureHom A B).hom

/-- **The sheaf of relative differentials `Ω_{𝒪/A}` on `C_{B/A}`**, a sheaf of `𝒪`-modules. It
is the objectwise module of Kähler differentials, which is already a sheaf because the topology
of `C_{B/A}` is chaotic; that it is the sheaf of differentials in the sense of Tag 04BL is
`CommAlgCat.polynomialRelativeDifferentialsCorepresentableBy`. -/
def polynomialRelativeDifferentials :
    SheafOfModules.{u + 1} (polynomialStructureRingSheaf A B) where
  val := polynomialRelativeDifferentialsPresheaf A B
  isSheaf := isSheaf_polynomialTopology A B _

/-- The universal relative derivation of `𝒪` over `A̲` with values in `Ω_{𝒪/A}`. -/
def polynomialUniversalDerivation :
    (polynomialRelativeDifferentials A B).val.Derivation'
      (polynomialBaseStructureHom A B).hom :=
  PresheafOfModules.DifferentialsConstruction.derivation' (polynomialBaseStructureHom A B).hom

/-- The sections of `Ω_{𝒪/A}` over the object `(P, α)` of `C_{B/A}` are the Kähler
differentials of the map of rings `A̲ ⟶ 𝒪` evaluated there, which by
`CommAlgCat.polynomialBaseStructureHom_app` is the universe lift of `A → P`. No sheafification
intervenes: the topology of `C_{B/A}` is chaotic, so `Ω_{𝒪/A}` is the objectwise module of
differentials. -/
theorem polynomialRelativeDifferentials_obj (X : polynomialSite A B) :
    (polynomialRelativeDifferentials A B).val.obj (op X) =
      CommRingCat.KaehlerDifferential ((polynomialBaseStructureHom A B).hom.app (op X)) :=
  rfl

/-- **The sections of `Ω_{𝒪/A}` over the object `(P, α)` of `C_{B/A}` are `Ω[P⁄A]`**, read
through the universe lift of `KaehlerDifferential.uliftLinearEquiv`: the sections are a module
over the value `ULift P` of the structure sheaf, and the identification sends `d x` to
`d x.down`. -/
def polynomialRelativeDifferentialsSectionsEquiv (X : polynomialSite A B) :
    letI : Module (ULift.{u + 1} (X.unop.obj.left : Type u))
        ((polynomialRelativeDifferentials A B).val.obj (op X)) :=
      ((polynomialRelativeDifferentials A B).val.obj (op X)).isModule
    ((polynomialRelativeDifferentials A B).val.obj (op X) : Type (u + 1)) ≃ₗ[ULift.{u + 1}
        (X.unop.obj.left : Type u)] Ω[(X.unop.obj.left : Type u)⁄A] :=
  KaehlerDifferential.uliftLinearEquiv.{u, u + 1} A (X.unop.obj.left : Type u)

/-- **Tag 04BL for the site `C_{B/A}`.** `Ω_{𝒪/A}` corepresents the functor sending a sheaf of
`𝒪`-modules to the relative derivations of `𝒪` over `A̲` with values in it, so it is the sheaf
of differentials of `A̲ ⟶ 𝒪`. Only the presheaf-level universal property of Mathlib's
`relativeDifferentials'` is used: every presheaf on `C_{B/A}` is a sheaf, so a morphism of
sheaves of modules is the same thing as a morphism of the underlying presheaves. -/
def polynomialRelativeDifferentialsCorepresentableBy :
    (AlgebraicGeometry.SheafOfModules.derivationsFunctor.{u + 1} (polynomialBaseSheaf A B)
        (polynomialStructureSheaf A B)
        (polynomialBaseStructureHom A B)).CorepresentableBy
      (polynomialRelativeDifferentials A B) := by
  refine AlgebraicGeometry.SheafOfModules.universalDerivationCorepresentableBy.{u + 1, u, u + 1,
    u + 1} _ _ _ (polynomialUniversalDerivation A B) (fun F D => ?_)
  refine ⟨⟨(PresheafOfModules.DifferentialsConstruction.isUniversal'
    (polynomialBaseStructureHom A B).hom).desc D⟩, ?_, fun g hg => ?_⟩
  · exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      (polynomialBaseStructureHom A B).hom).fac D
  · exact SheafOfModules.hom_ext
      ((PresheafOfModules.DifferentialsConstruction.isUniversal'
        (polynomialBaseStructureHom A B).hom).postcomp_injective _ _
          (hg.trans ((PresheafOfModules.DifferentialsConstruction.isUniversal'
            (polynomialBaseStructureHom A B).hom).fac D).symm))

/-! ### The base change `Ω_1 = B ⊗_𝒪 Ω_{𝒪/A}` -/

/-- The presheaf of `B̲`-modules `B̲ ⊗_𝒪 Ω_{𝒪/A}`, formed objectwise along the augmentation
`𝒪 ⟶ B̲` of Tag 08PR. -/
def polynomialRelativeDifferentialsBaseChangePresheaf :
    PresheafOfModules.{u + 1} (polynomialConstantRingSheaf A B).obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
    (polynomialAugmentation A B).hom).obj (polynomialRelativeDifferentials A B).val

/-- **The sheaf `Ω_1 = B̲ ⊗_𝒪 Ω_{𝒪/A}` on `C_{B/A}`**, a sheaf of `B̲`-modules: the base change
of the sheaf of relative differentials along the augmentation `𝒪 ⟶ B̲`. This is the sheaf the
source calls `Ω`, the one whose derived lower shriek is the cotangent complex `L_{B/A}`. The
objectwise tensor product is already a sheaf because the topology of `C_{B/A}` is chaotic. -/
def polynomialRelativeDifferentialsBaseChange :
    SheafOfModules.{u + 1} (polynomialConstantRingSheaf A B) where
  val := polynomialRelativeDifferentialsBaseChangePresheaf A B
  isSheaf := isSheaf_polynomialTopology A B _

/-- The sections of `Ω_1` over an object of `C_{B/A}` are the tensor product of the sections of
`B̲` with the sections of `Ω_{𝒪/A}` over the sections of `𝒪`, with no sheafification: the
`𝒪`-algebra structure on `B̲` is the augmentation. -/
theorem polynomialRelativeDifferentialsBaseChange_obj (W : (polynomialSite A B)ᵒᵖ) :
    letI : Algebra ((polynomialStructureSheaf A B).obj.obj W)
        ((polynomialConstantSheaf A B).obj.obj W) :=
      ((polynomialAugmentation A B).hom.app W).hom.toAlgebra
    letI : Module ((polynomialStructureSheaf A B).obj.obj W)
        ((polynomialRelativeDifferentials A B).val.obj W) :=
      ((polynomialRelativeDifferentials A B).val.obj W).isModule
    (polynomialRelativeDifferentialsBaseChange A B).val.obj W =
      ModuleCat.of ((polynomialConstantSheaf A B).obj.obj W)
        (TensorProduct ((polynomialStructureSheaf A B).obj.obj W)
          ((polynomialConstantSheaf A B).obj.obj W)
          ((polynomialRelativeDifferentials A B).val.obj W)) :=
  rfl

/-! ### Flatness of `Ω_{𝒪/A}` over `𝒪` -/

/-- **The differentials of a polynomial algebra are free.** If `P` is a polynomial algebra over
`A` in the sense of Tag 08QI then `Ω[P⁄A]` is a free `P`-module, on the variables. This is the
objectwise input to the flatness of `Ω_{𝒪/A}`, since every object of `C_{B/A}` is a polynomial
algebra. -/
theorem free_kaehlerDifferential_of_isPolynomialAlgebra {P : CommAlgCat.{u} A}
    (h : IsPolynomialAlgebra A P) : Module.Free (P : Type u) Ω[(P : Type u)⁄A] := by
  obtain ⟨ι, ⟨E⟩⟩ := h
  exact Module.Free.of_basis (KaehlerDifferential.basisOfMvPolynomialAlgEquiv E.symm)

/-- The identity, read as a comparison map from the presheaf of rings underlying `𝒪` to the
sheaf of rings underlying `𝒪`. Sheafification of presheaves of `𝒪`-modules is taken along
this map. -/
def polynomialRingUnit :
    (polynomialStructureSheaf A B).obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⟶
      (polynomialStructureRingSheaf A B).obj :=
  𝟙 _

/-- The map `CommAlgCat.polynomialRingUnit` is locally injective. -/
instance polynomialRingUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective (polynomialTopology A B) (polynomialRingUnit A B) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)

/-- The map `CommAlgCat.polynomialRingUnit` is locally surjective. -/
instance polynomialRingUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective (polynomialTopology A B) (polynomialRingUnit A B) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)

/-- `CommAlgCat.polynomialRingUnit` again, with its target spelled by
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are the same morphism,
but `Presheaf.IsLocallyInjective` is found by keyed instance matching and
`CommAlgCat.polynomialStructureRingSheaf` goes through the ringed topos of Tag 08PR, which is
not a reducible definition; so an instance for one spelling is not found for the other, and
Tag 0GN1 is stated at this one. -/
def polynomialRingUnitOfSite :
    (polynomialStructureSheaf A B).obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (polynomialStructureSheaf A B)).obj :=
  𝟙 _

/-- The map `CommAlgCat.polynomialRingUnitOfSite` is locally injective. -/
instance polynomialRingUnitOfSite_isLocallyInjective :
    Presheaf.IsLocallyInjective (polynomialTopology A B) (polynomialRingUnitOfSite A B) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)

/-- The map `CommAlgCat.polynomialRingUnitOfSite` is locally surjective. -/
instance polynomialRingUnitOfSite_isLocallySurjective :
    Presheaf.IsLocallySurjective (polynomialTopology A B) (polynomialRingUnitOfSite A B) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)

/-- The sheafification of `Ω_{𝒪/A}`, taken along `CommAlgCat.polynomialRingUnit`. Since the
topology of `C_{B/A}` is chaotic this is isomorphic to `Ω_{𝒪/A}`, but all that is used below
is that `Ω_{𝒪/A}` is a retract of it. -/
def polynomialRelativeDifferentialsSheafified :
    SheafOfModules.{u + 1} (polynomialStructureRingSheaf A B) :=
  (PresheafOfModules.sheafification (R := polynomialStructureRingSheaf A B)
    (polynomialRingUnit A B)).obj (polynomialRelativeDifferentials A B).val

/-- The unit of the sheafification adjunction, as a morphism of sheaves of `𝒪`-modules from
`Ω_{𝒪/A}` to its sheafification. -/
def polynomialRelativeDifferentialsToSheafified :
    polynomialRelativeDifferentials A B ⟶ polynomialRelativeDifferentialsSheafified A B :=
  ⟨(PresheafOfModules.sheafificationAdjunction (R := polynomialStructureRingSheaf A B)
    (polynomialRingUnit A B)).unit.app (polynomialRelativeDifferentials A B).val⟩

/-- The morphism that the sheafification adjunction attaches to the identity of `Ω_{𝒪/A}`,
which retracts the sheafification onto `Ω_{𝒪/A}`. -/
def polynomialRelativeDifferentialsFromSheafified :
    polynomialRelativeDifferentialsSheafified A B ⟶ polynomialRelativeDifferentials A B :=
  (PresheafOfModules.sheafificationHomEquiv (R := polynomialStructureRingSheaf A B)
    (polynomialRingUnit A B)).symm (𝟙 (polynomialRelativeDifferentials A B).val)

/-- `Ω_{𝒪/A}` is a retract of its sheafification, by the unit of the sheafification adjunction
and the morphism the adjunction attaches to the identity. -/
theorem polynomialRelativeDifferentials_retract :
    polynomialRelativeDifferentialsToSheafified A B ≫
        polynomialRelativeDifferentialsFromSheafified A B =
      𝟙 (polynomialRelativeDifferentials A B) := by
  refine SheafOfModules.hom_ext ?_
  show (PresheafOfModules.sheafificationHomEquiv (R := polynomialStructureRingSheaf A B)
    (polynomialRingUnit A B)) (polynomialRelativeDifferentialsFromSheafified A B) = _
  exact Equiv.apply_symm_apply _ _

/-- **`Ω_{𝒪/A}` is flat over `𝒪`.** Every object `(P, α)` of `C_{B/A}` has `P` a polynomial
algebra over `A`, so the value `Ω[P⁄A]` of `Ω_{𝒪/A}` is a free, hence flat, module over the
value `P` of `𝒪`; Tag 0GN1 turns objectwise flatness into flatness of the sheafification, and
`Ω_{𝒪/A}` is a retract of its sheafification. This is the input that lets the argument of Tag
08PU replace `Li^*` by `i^*`. -/
theorem polynomialRelativeDifferentials_isFlat :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u + 1, u + 1}
      (O := polynomialStructureSheaf A B) (polynomialRelativeDifferentials A B) := by
  have hsheafified :
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u + 1, u + 1}
        (O := polynomialStructureSheaf A B)
        (polynomialRelativeDifferentialsSheafified A B) := by
    refine Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat
      (polynomialTopology A B) (Osharp := polynomialStructureSheaf A B)
      (polynomialRingUnitOfSite A B) (polynomialRelativeDifferentials A B).val (fun U => ?_)
    refine ⟨PUnit.{u + 2}, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
    · rw [show Sieve.ofArrows (fun _ : PUnit.{u + 2} => U) (fun _ => 𝟙 U) = ⊤ from
        Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ PUnit.unit)]
      exact (polynomialTopology A B).top_mem U
    · exact KaehlerDifferential.flat_ulift_of_free.{u, u + 1} A (U.unop.obj.left : Type u)
        (free_kaehlerDifferential_of_isPolynomialAlgebra A U.unop.property)
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract _
    (polynomialRelativeDifferentialsToSheafified A B)
    (polynomialRelativeDifferentialsFromSheafified A B)
    (polynomialRelativeDifferentials_retract A B) hsheafified

end CommAlgCat

end
