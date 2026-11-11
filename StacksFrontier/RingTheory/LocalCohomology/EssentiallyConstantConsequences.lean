module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.RingTheory.LocalCohomology.BoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero
public import StacksFrontier.RingTheory.LocalCohomology.PuncturedSpectrumDescendingChain
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit

/-!
# Consequences of essential constancy for the local cohomology of adic quotients

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `T ⊆ Spec(A)` a specialization-stable subset of
`V(I)` and `M` a finite `A`-module, as in the bootstrap situation of [Stacks, Tag 0EFU]. Theorem
[Stacks, Tag 0EIE] asserts that for `i ≤ s` the inverse system `{H^i_T(M/IⁿM)}` is essentially
constant with value `H^i_T(M)`, and records three consequences of that assertion: the system is
Mittag-Leffler, `H^i_T(M)` is annihilated by a power of `I`, and `H^i_T(M)` is the inverse limit
of the system.

Those three consequences are what is proved here, each from the essential-constancy assertion
taken as an explicit hypothesis; the assertion itself is not proved here. Each of the three is a
genuine implication:

* essential constancy of an inverse system forces the images of its transition maps into a fixed
  term to stabilize, because the stable image is the image of the projection from the value;
* essential constancy exhibits the value as a retract of one term `H^i_T(M/IⁿM)`, and `H^i_T` is
  an `A`-linear functor, so the action of `a ∈ Iⁿ` on `H^i_T(M/IⁿM)` is the image of the zero
  endomorphism `a · id` of `M/IⁿM`, whence a retract of it is annihilated by `Iⁿ`;
* a cone carrying essential-constancy data is a limit cone.

Because the input of those three implications is the assertion of Tag 0EIE itself, none of them
carries a registration of the tag; the registrations in this file sit on the ranges where the
assertion is proved outright.

Two such ranges are here. In negative degrees the theorem holds unconditionally: `H^i_T` of a
module vanishes for `i < 0`, so every term of the system and the value are zero, and the zero
morphism witnesses essential constancy. When the depth bound `s` of the situation is itself
negative, every degree `i ≤ s` lies in that range, so the assertion and all four consequences
hold there with no hypothesis. And when `I` acts nilpotently on `M`, say `IᴺM = 0`, the quotient
maps `M → M/IᵐM` are isomorphisms for every `m ≥ N`; a cone whose projections are invertible
from an index on carries essential-constancy data, so the assertion and all four consequences
hold with no hypothesis in every degree there as well.

None of the three implications uses a hypothesis of the situation, so each is proved first for an
arbitrary commutative ring, ideal, subset of the spectrum and module, and then specialized to the
situation.

The converse direction is also proved here, in the shape the source's own proof takes it. That
proof reduces the assertion to three inputs — the Mittag-Leffler condition, the identification
`H^i_T(M) = lim H^i_T(M/IⁿM)` and the injectivity of `H^i_T(M) → H^i_T(M/IⁿM)` for `n ≫ 0` — and
`isEssentiallyConstantWith_localCohomologyAdicCone_of_isLimit` performs that reduction, with the
injectivity input traded for the descending chain condition on `H^i_T(M)`, which supplies it
once the cone is a limit cone.

For a bootstrap situation whose ring is local and whose locus `T` is the closed point, two of
those three inputs cost nothing: every `M/IⁿM` is a finite module, local cohomology at the
maximal ideal of a finite module over a Noetherian local ring is Artinian, and an inverse system
of Artinian modules is Mittag-Leffler. So in that case the Mittag-Leffler consequence holds with
no hypothesis and in every degree
(`Bootstrap.isMittagLeffler_of_eq_closedPoint`), and the essential-constancy assertion follows
from the limit identification alone
(`Bootstrap.isEssentiallyConstantWith_of_eq_closedPoint_of_isLimit`).

## Main definitions

* `Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor` — `H^i_T` as a functor on
  `A`-modules.
* `Stacks.LocalCohomology.idealPowerQuotientTower` and
  `Stacks.LocalCohomology.idealPowerQuotientCone` — the inverse system `M/IⁿM` and the cone on it
  given by the quotient maps out of `M`.
* `Stacks.LocalCohomology.localCohomologyAdicTower` and
  `Stacks.LocalCohomology.localCohomologyAdicCone` — their images under `H^i_T`.

## Main results

* `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith.isLimit` — a cone carrying
  essential-constancy data is a limit cone.
* `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith.isMittagLefflerCategorical` —
  an essentially constant inverse system over an abelian category is Mittag-Leffler.
* `CategoryTheory.EssentiallyConstantPro.exists_isEssentiallyConstantWith_of_isIso_π` — a cone on
  an `ℕᵒᵖ`-indexed diagram whose projections are invertible from some index on carries
  essential-constancy data.
* `Stacks.LocalCohomology.derivedSectionsWithSupportIn_linear` — `RΓ_T` is `A`-linear, hence so
  is `H^i_T`.
* `Stacks.LocalCohomology.exists_pow_smul_eq_zero_of_isEssentiallyConstantWith` and
  `Stacks.LocalCohomology.isLimit_localCohomologyAdicCone_of_isEssentiallyConstantWith` — the
  annihilation and the limit consequence for an arbitrary commutative ring, ideal, subset and
  module.
* `Stacks.LocalCohomology.Bootstrap.isMittagLeffler`,
  `Stacks.LocalCohomology.Bootstrap.exists_pow_smul_eq_zero`,
  `Stacks.LocalCohomology.Bootstrap.isLimit` and
  `Stacks.LocalCohomology.Bootstrap.isIso_limitLift` — the three consequences in the bootstrap
  situation, from the essential-constancy assertion as a hypothesis.
* `Stacks.LocalCohomology.isEssentiallyConstantWith_localCohomologyAdicCone_of_neg` — the
  unconditional statement in negative degrees.
* `Stacks.LocalCohomology.Bootstrap.isEssentiallyConstantWith_of_depthBound_neg` — the
  unconditional statement for a bootstrap situation whose depth bound `s` is negative, where
  every degree `i ≤ s` falls in that range.
* `Stacks.LocalCohomology.isIso_idealPowerQuotientCone_π` and
  `exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_pow_smul_top_eq_bot` — if
  `IᴺM = 0` the quotient maps `M → M/IᵐM` are invertible for `m ≥ N`, and the unconditional
  statement in every degree follows.
* `Stacks.LocalCohomology.Bootstrap.exists_isEssentiallyConstantWith_of_pow_smul_top_eq_bot`,
  `Stacks.LocalCohomology.Bootstrap.isMittagLeffler_of_pow_smul_top_eq_bot`,
  `Stacks.LocalCohomology.Bootstrap.exists_pow_smul_eq_zero_of_pow_smul_top_eq_bot` and
  `Stacks.LocalCohomology.Bootstrap.isLimit_of_pow_smul_top_eq_bot` — the assertion and its three
  consequences for a bootstrap situation in which `I` acts nilpotently on `M`, with no hypothesis
  and in every degree.
* `Stacks.LocalCohomology.isEssentiallyConstantWith_localCohomologyAdicCone_of_isLimit` — the
  assertion from its three inputs: the cone is a limit cone, the system is Mittag-Leffler, and
  `H^i_T(M)` has the descending chain condition.
* `Stacks.LocalCohomology.isArtinian_localCohomologyWithSupportIn_closedPoint` and
  `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint` —
  over a Noetherian local ring with `T` the closed point and `M` finite, the value and all the
  terms are Artinian and the system is Mittag-Leffler, with no hypothesis; these are the two of
  the three inputs above that are free in that case.
* `Stacks.LocalCohomology.Bootstrap.isMittagLeffler_of_eq_closedPoint` — the Mittag-Leffler
  consequence for a bootstrap situation at the closed point of a local ring, with no hypothesis.
* `Stacks.LocalCohomology.Bootstrap.isEssentiallyConstantWith_of_eq_closedPoint_of_isLimit` —
  the assertion there, from the limit identification alone.

## Implementation notes

The `A`-linearity of `H^i_T` is not formal: `RΓ_T` is a total right derived functor, so the
linearity of the underlying functor on complexes is transported through the canonical comparison
`derivedSectionsWithSupportInUnit`, which is invertible on K-injective complexes, and then across
an isomorphism to an arbitrary object of `D(A)`.

The essential-constancy hypothesis is stated as
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith` for the tower
`localCohomologyAdicTower` and the cone `localCohomologyAdicCone`, whose point is `H^i_T(M)`;
this is the assertion of Tag 0EIE verbatim, with the witnessing index and retraction exposed in
the signature.

The closed-point statements take the module universe equal to the ring universe, because
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule` — the agreement of
the supported-sections model used here with the coreflection model of [Stacks, Tag 0A6Q], which
is where the Artinianness of [Stacks, Tag 0DX0] is available — is stated only there.

### Where the assertion is proved

Theorem [Stacks, Tag 0EIE] itself, in Situation [Stacks, Tag 0EFU] at a general
specialization-stable `T`, is
`Stacks.LocalCohomology.Bootstrap.essentiallyConstant_and_consequences`, in
`StacksFrontier/RingTheory/LocalCohomology/EssentiallyConstantBootstrap.lean`. In that situation both
assertions of [Stacks, Tag 0EFX] are
`Stacks.Algebraization.isProZero_and_hasStableImage_idealPowerCohomology`, and all seven parts of
[Stacks, Tag 0EFY], at one and the same `m₀`, are
`Stacks.Algebraization.exists_bound_adicLocalCohomologyComparisons`.

## References

* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFY](https://stacks.math.columbia.edu/tag/0EFY)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0DX0](https://stacks.math.columbia.edu/tag/0DX0)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory.EssentiallyConstantPro

section Limit

variable {J : Type*} [Category J] {C : Type*} [Category C] {F : J ⥤ C} {c : Cone F} {j : J}
  {s : F.obj j ⟶ c.pt}

/-- A cone carrying essential-constancy data is a limit cone. This is the exact dual of
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.isColimit`, and neither
smallness nor cofilteredness of the index category is used.

*Argument.* Given any cone `t = (Y, {d_l})`, the morphism `d_j ≫ s : Y ⟶ c.pt` is a factorization:
for each `l`, pick `k`, `σ : k ⟶ j`, `τ : k ⟶ l` from cofinality with
`F τ = F σ ≫ s ≫ p_l`, and compute
`d_l = d_k ≫ F τ = d_k ≫ F σ ≫ s ≫ p_l = d_j ≫ s ≫ p_l`. It is the only one: if
`u ≫ p_l = d_l` for all `l`, then `u = u ≫ (p_j ≫ s) = d_j ≫ s` by the retraction clause. -/
def IsEssentiallyConstantWith.isLimit (h : IsEssentiallyConstantWith F c j s) : IsLimit c where
  lift t := t.π.app j ≫ s
  fac t l := by
    obtain ⟨k, σ, τ, hkστ⟩ := h.cofinal l
    rw [← t.w τ, hkστ, ← t.w σ]
    simp only [Category.assoc]
  uniq t u hu := by
    rw [← Category.comp_id u, ← h.retraction, ← Category.assoc, hu j]

end Limit

section IsoProjections

variable {C : Type*} [Category C] {F : ℕᵒᵖ ⥤ C}

/-- **A cone on an inverse system whose projections are invertible from some index on carries
essential-constancy data.** If `c.π.app (op m)` is an isomorphism for every `m ≥ n`, then `F` is
essentially constant with value `c.pt` with respect to `c` itself, witnessed at the index `op n`
by the inverse of `c.π.app (op n)`.

*Argument.* The retraction clause is `hom_inv_id` for `c.π.app (op n)`. For cofinality at an
index `l` take `k = max n l.unop`, where the projection is invertible too; cancelling the
epimorphism `c.π.app (op k)` and using the cone's naturality twice turns both sides of the
required equation into `c.π.app l`. -/
theorem exists_isEssentiallyConstantWith_of_isIso_π (c : Cone F) (n : ℕ)
    (h : ∀ m : ℕ, n ≤ m → IsIso (c.π.app (op m))) :
    ∃ (j : ℕᵒᵖ) (s : F.obj j ⟶ c.pt), IsEssentiallyConstantWith F c j s := by
  have hn := h n le_rfl
  refine ⟨op n, inv (c.π.app (op n)), IsIso.hom_inv_id _, fun l => ?_⟩
  have hk := h (max n l.unop) (le_max_left n l.unop)
  refine ⟨op (max n l.unop), (homOfLE (le_max_left n l.unop)).op,
    (homOfLE (le_max_right n l.unop)).op, ?_⟩
  rw [← cancel_epi (c.π.app (op (max n l.unop))), c.w, ← Category.assoc, c.w,
    IsIso.hom_inv_id_assoc]

end IsoProjections

section MittagLeffler

variable {C : Type*} [Category C] [Abelian C] {F : ℕᵒᵖ ⥤ C} {c : Cone F} {j : ℕᵒᵖ}
  {s : F.obj j ⟶ c.pt}

private theorem transitionImage_eq_imageSubobject (i k : ℕ) (h : i ≤ k) :
    transitionImage F i k h = imageSubobject (F.map (homOfLE h).op) := rfl

/-- **An essentially constant inverse system over an abelian category is Mittag-Leffler.**

*Argument.* Fix a term `A_i`. Cofinality supplies an index `c ≥ i` through which the transition
map `A_c → A_i` factors as `A_c → A_j → c.pt → A_i`, so its image is contained in the image of
the projection `p_i : c.pt → A_i`. Conversely `p_i = p_k ≫ (A_k → A_i)` for every `k ≥ i`, so the
image of `p_i` is contained in the image of every transition map into `A_i`. Since the images of
the transition maps into `A_i` decrease, they are all equal to the image of `p_i` from `c` on. -/
theorem IsEssentiallyConstantWith.isMittagLefflerCategorical
    (h : IsEssentiallyConstantWith F c j s) : IsMittagLefflerCategorical F := by
  intro i
  obtain ⟨k, σ, τ, hkστ⟩ := h.cofinal (op i)
  have hik : i ≤ k.unop := leOfHom τ.unop
  refine ⟨k.unop, hik, fun m hkm => ?_⟩
  have key : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {e : X ⟶ Z}, e = f ≫ g →
      imageSubobject e ≤ imageSubobject g := by
    rintro X Y Z f g e rfl
    exact imageSubobject_comp_le f g
  have hle₁ := key (F.map (homOfLE hkm).op) (F.map (homOfLE hik).op)
    (F.map_comp (homOfLE hkm).op (homOfLE hik).op)
  have hle₂ := (key (F.map σ) (s ≫ c.π.app (op i)) (e := F.map (homOfLE hik).op) hkστ).trans
    (key s (c.π.app (op i)) rfl)
  have hle₃ := key (c.π.app (op m)) (F.map (homOfLE (hik.trans hkm)).op)
    (e := c.π.app (op i)) (c.w _).symm
  rw [transitionImage_eq_imageSubobject, transitionImage_eq_imageSubobject]
  exact le_antisymm hle₁ (hle₂.trans hle₃)

end MittagLeffler

end CategoryTheory.EssentiallyConstantPro

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-! ### `A`-linearity of local cohomology with support in `T` -/

/-! ### The functor `H^i_T` and the tower `M/IⁿM` -/

/-- Local cohomology with support in `T` is `A`-linear in the module. -/
instance localCohomologyWithSupportInModuleFunctor_linear (i : ℤ) :
    Functor.Linear A (localCohomologyWithSupportInModuleFunctor.{u, v} A T i) := by
  unfold localCohomologyWithSupportInModuleFunctor
  infer_instance

/-- `H^i_T` of a module is the local cohomology of that module placed in degree zero. -/
theorem localCohomologyWithSupportInModuleFunctor_obj (i : ℤ) (M : ModuleCat.{max u v} A) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M =
      localCohomologyWithSupportIn.{u, v} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i := rfl

variable {A}

/-- The inverse system `M/IⁿM` of quotients of `M` by the powers of `I`, with the transition maps
induced by the identity of `M`. -/
def idealPowerQuotientTower (I : Ideal A) (M : ModuleCat.{max u v} A) :
    ℕᵒᵖ ⥤ ModuleCat.{max u v} A where
  obj n := ModuleCat.of A (M ⧸ (I ^ n.unop • (⊤ : Submodule A M)))
  map {m n} g := ModuleCat.ofHom <|
    Submodule.mapQ (I ^ m.unop • (⊤ : Submodule A M)) (I ^ n.unop • (⊤ : Submodule A M))
      LinearMap.id (by
        simpa using Submodule.smul_mono_left (Ideal.pow_le_pow_right (leOfHom g.unop)))
  map_id _ := by apply ModuleCat.hom_ext; ext x; rfl
  map_comp _ _ := by apply ModuleCat.hom_ext; ext x; rfl

/-- The cone on the tower `M/IⁿM` with point `M`, given by the quotient maps. -/
def idealPowerQuotientCone (I : Ideal A) (M : ModuleCat.{max u v} A) :
    Cone (idealPowerQuotientTower I M) :=
  Cone.mk M
    { app n := ModuleCat.ofHom (Submodule.mkQ (I ^ n.unop • (⊤ : Submodule A M)))
      naturality := by
        intro m n g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        rfl }

/-- An element of `Iⁿ` annihilates `M/IⁿM`: scaling the identity of the `n`-th term of the tower
by it gives the zero endomorphism. -/
theorem smul_id_idealPowerQuotientTower_eq_zero (I : Ideal A) (M : ModuleCat.{max u v} A)
    (n : ℕᵒᵖ) {a : A} (ha : a ∈ I ^ n.unop) :
    a • 𝟙 ((idealPowerQuotientTower I M).obj n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n.unop • (⊤ : Submodule A M)) x
  change a • (Submodule.Quotient.mk y : M ⧸ (I ^ n.unop • (⊤ : Submodule A M))) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- An element of `Iⁿ` kills the `n`-th quotient map `M → M/IⁿM` of the tower. -/
theorem smul_idealPowerQuotientCone_app_eq_zero (I : Ideal A) (M : ModuleCat.{max u v} A)
    (n : ℕᵒᵖ) {a : A} (ha : a ∈ I ^ n.unop) :
    a • (idealPowerQuotientCone I M).π.app n = 0 :=
  calc a • (idealPowerQuotientCone I M).π.app n
      = (idealPowerQuotientCone I M).π.app n ≫ (a • 𝟙 ((idealPowerQuotientTower I M).obj n)) := by
        rw [Linear.comp_smul, Category.comp_id]
    _ = 0 := by rw [smul_id_idealPowerQuotientTower_eq_zero I M n ha, comp_zero]

/-- **If `I` acts nilpotently on `M` the quotient maps of the tower are invertible from the
nilpotency exponent on.** If `IᴺM = 0` then `IᵐM = 0` for every `m ≥ N`, so the `m`-th quotient
map `M → M/IᵐM` is the quotient by the zero submodule; its inverse is the map lifting the
identity of `M` through that quotient. -/
theorem isIso_idealPowerQuotientCone_π (I : Ideal A) (M : ModuleCat.{max u v} A) {N : ℕ}
    (hN : I ^ N • (⊤ : Submodule A M) = ⊥) {m : ℕ} (hm : N ≤ m) :
    IsIso ((idealPowerQuotientCone I M).π.app (op m)) := by
  have hbot : I ^ m • (⊤ : Submodule A M) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hN]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hm)
  have hker : I ^ m • (⊤ : Submodule A M) ≤
      LinearMap.ker (LinearMap.id : M →ₗ[A] M) :=
    hbot.le.trans bot_le
  refine ⟨ModuleCat.ofHom ((I ^ m • (⊤ : Submodule A M)).liftQ LinearMap.id hker), ?_, ?_⟩
  · exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ m • (⊤ : Submodule A M)) x
    rfl

variable (A)

/-- The inverse system `{H^i_T(M/IⁿM)}` of local cohomology modules of the adic quotients. -/
abbrev localCohomologyAdicTower (I : Ideal A) (i : ℤ) (M : ModuleCat.{max u v} A) :
    ℕᵒᵖ ⥤ ModuleCat.{max u v} A :=
  idealPowerQuotientTower I M ⋙ localCohomologyWithSupportInModuleFunctor.{u, v} A T i

/-- The cone on `{H^i_T(M/IⁿM)}` with point `H^i_T(M)` obtained by applying `H^i_T` to the
quotient maps `M → M/IⁿM`. "Essentially constant with value `H^i_T(M)`" means essentially
constant with respect to this cone. -/
abbrev localCohomologyAdicCone (I : Ideal A) (i : ℤ) (M : ModuleCat.{max u v} A) :
    Cone (localCohomologyAdicTower.{u, v} A T I i M) :=
  (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).mapCone (idealPowerQuotientCone I M)

/-! ### The three consequences

Each is derived from the essential-constancy assertion of Tag 0EIE taken as a hypothesis. -/

/-- A retract of a module annihilated by `a` is annihilated by `a`, in the form used below: if the
`n`-th projection of a cone `c` is killed by `a` and the image of that projection under an
`A`-linear functor `H` admits a retraction, then `a` annihilates `H(c.pt)`. Indeed
`a • 𝟙 (H(c.pt)) = (a • H(p_n)) ≫ σ = H(a • p_n) ≫ σ` is zero. -/
private theorem smul_eq_zero_of_isEssentiallyConstantWith
    (H : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A) [Functor.Linear A H]
    {G : ℕᵒᵖ ⥤ ModuleCat.{max u v} A} (c : Cone G) (n : ℕᵒᵖ) {a : A}
    (hq : a • c.π.app n = 0) {σ : (G ⋙ H).obj n ⟶ (H.mapCone c).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith (G ⋙ H) (H.mapCone c) n σ)
    (z : (H.mapCone c).pt) : a • z = 0 := by
  have hret : H.map (c.π.app n) ≫ σ = 𝟙 (H.obj c.pt) := h.retraction
  have hmapzero : H.map (0 : ((Functor.const ℕᵒᵖ).obj c.pt).obj n ⟶ G.obj n) = 0 := by
    rw [← zero_smul A (0 : ((Functor.const ℕᵒᵖ).obj c.pt).obj n ⟶ G.obj n), Functor.map_smul,
      zero_smul]
  have key : a • 𝟙 (H.obj c.pt) = 0 := by
    rw [← hret, ← Linear.smul_comp, ← Functor.map_smul, hq, hmapzero, zero_comp]
  exact congrArg (fun f : H.obj c.pt ⟶ H.obj c.pt => f.hom z) key

/-- The value of an essentially constant system of local cohomology modules of the adic quotients
is annihilated by a power of `I`.

*Argument.* The retraction clause exhibits `H^i_T(M)` as a retract of `H^i_T(M/IⁿM)` along
`H^i_T(M → M/IⁿM)`. For `a ∈ Iⁿ` the endomorphism `a · id` of `M/IⁿM` is zero, so `a` times the
quotient map `M → M/IⁿM` is zero, and `H^i_T` is `A`-linear, so `a` times its image is zero;
composing with the retraction gives `a • 𝟙 (H^i_T(M)) = 0`. -/
theorem exists_pow_smul_eq_zero_of_isEssentiallyConstantWith (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{max u v} A) {j : ℕᵒᵖ}
    {σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      j σ) :
    ∃ n : ℕ, ∀ a ∈ I ^ n,
      ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M, a • x = 0 :=
  ⟨j.unop, fun _ ha x =>
    smul_eq_zero_of_isEssentiallyConstantWith A
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i) (idealPowerQuotientCone I M) j
      (smul_idealPowerQuotientCone_app_eq_zero I M j ha) h x⟩

/-- The canonical cone on the system `{H^i_T(M/IⁿM)}` with point `H^i_T(M)` is a limit cone as
soon as it carries essential-constancy data. -/
def isLimit_localCohomologyAdicCone_of_isEssentiallyConstantWith (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{max u v} A) {j : ℕᵒᵖ}
    {σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      j σ) :
    IsLimit (localCohomologyAdicCone.{u, v} A T I i M) :=
  h.isLimit

/-! ### Negative degrees, unconditionally -/

/-- **Stacks Project, Tag 0EIE** in negative degrees, with no hypothesis.
For `i < 0` the system `{H^i_T(M/IⁿM)}` is essentially constant with value `H^i_T(M)`: local
cohomology with support in `T` of a module vanishes in negative degrees
(`Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_single_of_neg`), so every term of
the system and the value are zero and the zero morphism is a witness. The three consequences in
this range follow by composing with the implications above. -/
@[stacks 0EIE "the negative-degree range, unconditionally: for i < 0 the system is essentially
constant with value H^i_T(M) = 0"]
theorem isEssentiallyConstantWith_localCohomologyAdicCone_of_neg (I : Ideal A) (i : ℤ)
    (hi : i < 0) (M : ModuleCat.{max u v} A) :
    EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      (op 0) 0 where
  retraction :=
    (isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T M i hi).eq_of_tgt _ _
  cofinal l :=
    ⟨l, homOfLE (Nat.zero_le l.unop) |>.op, 𝟙 l,
      (isZero_localCohomologyWithSupportIn_single_of_neg.{u, v} A T
        ((idealPowerQuotientTower I M).obj l) i hi).eq_of_tgt _ _⟩

/-! ### A nilpotent ideal action, unconditionally -/

/-- **Stacks Project, Tag 0EIE** when `I` acts nilpotently on `M`, with no hypothesis and in
every degree. If `IᴺM = 0` then the quotient maps `M → M/IᵐM` are isomorphisms for every
`m ≥ N`, hence so are their images under `H^i_T`, and a cone whose projections are invertible
from an index on carries essential-constancy data
(`CategoryTheory.EssentiallyConstantPro.exists_isEssentiallyConstantWith_of_isIso_π`). The three
consequences in this range follow by composing with the implications above.

No Noetherian, finiteness or support hypothesis is used: `A` is an arbitrary commutative ring,
`T` an arbitrary subset of its spectrum and `M` an arbitrary module. -/
@[stacks 0EIE "the range where I acts nilpotently on M: if I^N M = 0 then in every degree the
system is essentially constant with value H^i_T(M), for an arbitrary ring, subset of the
spectrum and module"]
theorem exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_pow_smul_top_eq_bot
    (I : Ideal A) (i : ℤ) (M : ModuleCat.{max u v} A) {N : ℕ}
    (hN : I ^ N • (⊤ : Submodule A M) = ⊥) :
    ∃ (j : ℕᵒᵖ) (σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
        (localCohomologyAdicCone.{u, v} A T I i M).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
        j σ :=
  EssentiallyConstantPro.exists_isEssentiallyConstantWith_of_isIso_π
    (localCohomologyAdicCone.{u, v} A T I i M) N fun m hm => by
      have h := isIso_idealPowerQuotientCone_π I M hN hm
      change IsIso ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerQuotientCone I M).π.app (op m)))
      infer_instance

/-! ### The assertion from the limit identification

The source's proof opens by reducing the essential-constancy assertion to three inputs: the
Mittag-Leffler condition on `{H^i_T(M/IⁿM)}`, the identification `H^i_T(M) = lim H^i_T(M/IⁿM)`,
and the injectivity of `H^i_T(M) → H^i_T(M/IⁿM)` for `n ≫ 0`. That reduction is
`Stacks.LocalCohomology.isEssentiallyConstantWith_of_isMittagLeffler_of_eventually_injective`;
below it is applied to the tower and cone of Tag 0EIE, with the injectivity input traded for the
descending chain condition on `H^i_T(M)`, which supplies it once the cone is known to be a limit
cone. -/

/-- **The essential-constancy assertion of [Stacks, Tag 0EIE] from its three inputs.** If the
canonical cone on `{H^i_T(M/IⁿM)}` with point `H^i_T(M)` is a limit cone, the system is
Mittag-Leffler and `H^i_T(M)` has the descending chain condition, then the system is essentially
constant with value `H^i_T(M)`, with respect to that cone.

The third hypothesis replaces the eventual injectivity of `H^i_T(M) → H^i_T(M/IⁿM)` that the
source quotes from Lemma [Stacks, Tag 0EFY]: the kernels of those maps form a descending chain
in `H^i_T(M)`, so they stabilize, and a limit cone has zero intersection of kernels. -/
theorem isEssentiallyConstantWith_localCohomologyAdicCone_of_isLimit (I : Ideal A) (i : ℤ)
    (M : ModuleCat.{max u v} A) (hlim : IsLimit (localCohomologyAdicCone.{u, v} A T I i M))
    (hML : IsMittagLefflerCategorical (localCohomologyAdicTower.{u, v} A T I i M))
    (hArt : IsArtinian A ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M)) :
    ∃ (j : ℕᵒᵖ) (σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
        (localCohomologyAdicCone.{u, v} A T I i M).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
        j σ :=
  isEssentiallyConstantWith_of_isMittagLeffler_of_isArtinian hlim hML hArt

/-! ### Support at the closed point of a Noetherian local ring

For `T = {𝔪}` over a Noetherian local ring and `M` finite, two of the three inputs above are
unconditional, because every module in sight is Artinian. -/

/-- Local cohomology with support at the closed point of a Noetherian local ring, of a finite
module, has the descending chain condition in every degree.

The closed point is the zero locus of the maximal ideal, so the supported-sections model used
here agrees with the coreflection model of [Stacks, Tag 0A6Q] by
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`, and in that model
the statement is part (1) of [Stacks, Tag 0DX0]. -/
theorem isArtinian_localCohomologyWithSupportIn_closedPoint [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ) :
    IsArtinian A ((localCohomologyWithSupportInModuleFunctor.{u, u} A
      {IsLocalRing.closedPoint A} i).obj M) := by
  have hT : ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) =
      PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A) :=
    zeroLocus_maximalIdeal.symm
  have hart : IsArtinian A (localCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i) :=
    isArtinian_localCohomology_maximalIdeal A M i
  rw [hT]
  exact isArtinian_of_linearEquiv
    (localCohomologyWithSupportInIsoLocalCohomologyModule A (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing M i).symm.toLinearEquiv

/-- **The inverse system `{H^i_𝔪(M/IⁿM)}` over a Noetherian local ring is Mittag-Leffler**, with
no hypothesis: each `M/IⁿM` is a finite module, so each term has the descending chain condition,
and the images of the transition maps into a fixed term then stabilize.

This is part (2) of [Stacks, Tag 0EFY] at `T = {𝔪}`, in the model Tag 0EIE is phrased with
here; `Stacks.LocalCohomology.isMittagLefflerCategorical_homologyAdicQuotientLocalCohomology`
carries that registration for the coreflection model and the tower of Tag 0EEW. For a general
specialization-stable `T ⊆ V(I)` the terms are neither finite nor Artinian and the source
obtains the Mittag-Leffler condition from the pro-zero assertion of [Stacks, Tag 0EFX]
instead. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint [IsLocalRing A]
    [IsNoetherianRing A] (I : Ideal A) (i : ℤ) (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsMittagLefflerCategorical
      (localCohomologyAdicTower.{u, u} A {IsLocalRing.closedPoint A} I i M) := by
  refine isMittagLefflerCategorical_of_isArtinian _ fun n => ?_
  have : Module.Finite A ((idealPowerQuotientTower.{u, u} I M).obj n) :=
    Module.Finite.quotient A _
  exact isArtinian_localCohomologyWithSupportIn_closedPoint A
    ((idealPowerQuotientTower.{u, u} I M).obj n) i

/-! ### The theorem in the bootstrap situation -/

namespace Bootstrap

open Stacks.Algebraization

variable (S : BootstrapSituation.{u, max u v, w}) (i : ℤ)

/-- The system `{H^i_T(M/IⁿM)}` of the bootstrap situation. -/
abbrev tower : ℕᵒᵖ ⥤ ModuleCat.{max u v} S.A :=
  localCohomologyAdicTower.{u, v} S.A S.T S.I i (ModuleCat.of S.A S.M)

/-- The cone on `{H^i_T(M/IⁿM)}` with point `H^i_T(M)` in the bootstrap situation. -/
abbrev cone : Cone (tower.{u, v} S i) :=
  localCohomologyAdicCone.{u, v} S.A S.T S.I i (ModuleCat.of S.A S.M)

/-- **Stacks Project, Tag 0EIE**, first consequence. In the bootstrap situation, if for `i ≤ s`
the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value `H^i_T(M)`, then it
satisfies the Mittag-Leffler condition.

Only the essential constancy is used; the hypotheses of the situation enter the theorem of the
source solely through the essential-constancy assertion, which is a hypothesis here. Because
that assertion is the content of Tag 0EIE itself, this implication carries no registration of
the tag; the registrations of Tag 0EIE in this file sit on the ranges where the assertion is
proved. -/
theorem isMittagLeffler (_hi : i ≤ S.s) {j : ℕᵒᵖ}
    {σ : (tower.{u, v} S i).obj j ⟶ (cone.{u, v} S i).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (tower.{u, v} S i) (cone.{u, v} S i) j σ) :
    IsMittagLefflerCategorical (tower.{u, v} S i) :=
  h.isMittagLefflerCategorical

/-- **Stacks Project, Tag 0EIE**, second consequence. In the bootstrap situation, if for `i ≤ s`
the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value `H^i_T(M)`, then
`H^i_T(M)` is annihilated by a power of `I`.

The input is the content of Tag 0EIE itself, so this implication carries no registration of the
tag. -/
theorem exists_pow_smul_eq_zero (_hi : i ≤ S.s) {j : ℕᵒᵖ}
    {σ : (tower.{u, v} S i).obj j ⟶ (cone.{u, v} S i).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (tower.{u, v} S i) (cone.{u, v} S i) j σ) :
    ∃ n : ℕ, ∀ a ∈ S.I ^ n,
      ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, v} S.A S.T i).obj
        (ModuleCat.of S.A S.M), a • x = 0 :=
  exists_pow_smul_eq_zero_of_isEssentiallyConstantWith S.A S.T S.I i _ h

/-- **Stacks Project, Tag 0EIE**, third consequence. In the bootstrap situation, if for `i ≤ s`
the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value `H^i_T(M)`, then the
canonical maps `H^i_T(M) → H^i_T(M/IⁿM)` exhibit `H^i_T(M)` as the inverse limit
`lim H^i_T(M/IⁿM)`.

The input is the content of Tag 0EIE itself, so this implication carries no registration of the
tag. -/
def isLimit (_hi : i ≤ S.s) {j : ℕᵒᵖ}
    {σ : (tower.{u, v} S i).obj j ⟶ (cone.{u, v} S i).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (tower.{u, v} S i) (cone.{u, v} S i) j σ) :
    IsLimit (cone.{u, v} S i) :=
  h.isLimit

/-- **Stacks Project, Tag 0EIE**, third consequence in comparison form. In the bootstrap
situation, if for `i ≤ s` the inverse system `{H^i_T(M/IⁿM)}` is essentially constant with value
`H^i_T(M)`, then `lim H^i_T(M/IⁿM)` exists and the canonical comparison
`H^i_T(M) → lim H^i_T(M/IⁿM)` induced by the maps `H^i_T(M) → H^i_T(M/IⁿM)` is an isomorphism.

The input is the content of Tag 0EIE itself, so this implication carries no registration of the
tag. -/
theorem isIso_limitLift (_hi : i ≤ S.s) {j : ℕᵒᵖ}
    {σ : (tower.{u, v} S i).obj j ⟶ (cone.{u, v} S i).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (tower.{u, v} S i) (cone.{u, v} S i) j σ) :
    letI : HasLimit (tower.{u, v} S i) := HasLimit.mk ⟨cone.{u, v} S i, h.isLimit⟩
    IsIso (limit.lift (tower.{u, v} S i) (cone.{u, v} S i)) := by
  let : HasLimit (tower.{u, v} S i) := HasLimit.mk ⟨cone.{u, v} S i, h.isLimit⟩
  change IsIso (limit.lift (tower.{u, v} S i) (cone.{u, v} S i))
  have heq : limit.lift (tower.{u, v} S i) (cone.{u, v} S i) =
      (h.isLimit.conePointUniqueUpToIso (limit.isLimit (tower.{u, v} S i))).hom := by
    apply limit.hom_ext
    intro n
    rw [limit.lift_π]
    exact (IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit
      (limit.isLimit (tower.{u, v} S i)) n).symm
  rw [heq]
  infer_instance

/-- **Stacks Project, Tag 0EIE** for a bootstrap situation whose depth bound is negative. Every
degree `i ≤ s < 0` is negative, so each term of `{H^i_T(M/IⁿM)}` and the value `H^i_T(M)`
vanish and the zero morphism witnesses essential constancy with value `H^i_T(M)`. The four
consequences above apply to this witness, and so hold with no hypothesis in this range. -/
@[stacks 0EIE "the essential-constancy assertion, and with it the four consequences, for a
bootstrap situation whose depth bound s is negative"]
theorem isEssentiallyConstantWith_of_depthBound_neg (hs : S.s < 0) (hi : i ≤ S.s) :
    EssentiallyConstantPro.IsEssentiallyConstantWith
      (tower.{u, v} S i) (cone.{u, v} S i) (op 0) 0 :=
  isEssentiallyConstantWith_localCohomologyAdicCone_of_neg.{u, v} S.A S.T S.I i (hi.trans_lt hs)
    (ModuleCat.of S.A S.M)

/-- **Stacks Project, Tag 0EIE** for a bootstrap situation in which `I` acts nilpotently on `M`,
with no hypothesis and in every degree. The quotient maps `M → M/IᵐM` are isomorphisms from the
nilpotency exponent on, so the canonical cone's projections are, and a cone whose projections
are invertible from an index on carries essential-constancy data. -/
@[stacks 0EIE "the essential-constancy assertion for a bootstrap situation in which I acts
nilpotently on M, with no hypothesis and in every degree"]
theorem exists_isEssentiallyConstantWith_of_pow_smul_top_eq_bot {N : ℕ}
    (hN : S.I ^ N • (⊤ : Submodule S.A S.M) = ⊥) :
    ∃ (j : ℕᵒᵖ) (σ : (tower.{u, v} S i).obj j ⟶ (cone.{u, v} S i).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (tower.{u, v} S i) (cone.{u, v} S i) j σ :=
  exists_isEssentiallyConstantWith_localCohomologyAdicCone_of_pow_smul_top_eq_bot.{u, v}
    S.A S.T S.I i (ModuleCat.of S.A S.M) hN

/-- **Stacks Project, Tag 0EIE**, the Mittag-Leffler consequence for a bootstrap situation in
which `I` acts nilpotently on `M`, with no hypothesis and in every degree. -/
@[stacks 0EIE "the Mittag-Leffler consequence for a bootstrap situation in which I acts
nilpotently on M, with no hypothesis and in every degree"]
theorem isMittagLeffler_of_pow_smul_top_eq_bot {N : ℕ}
    (hN : S.I ^ N • (⊤ : Submodule S.A S.M) = ⊥) :
    IsMittagLefflerCategorical (tower.{u, v} S i) :=
  let ⟨_, _, h⟩ := exists_isEssentiallyConstantWith_of_pow_smul_top_eq_bot.{u, v} S i hN
  h.isMittagLefflerCategorical

/-- **Stacks Project, Tag 0EIE**, the annihilation consequence for a bootstrap situation in which
`I` acts nilpotently on `M`, with no hypothesis and in every degree. -/
@[stacks 0EIE "the annihilation consequence for a bootstrap situation in which I acts nilpotently
on M, with no hypothesis and in every degree"]
theorem exists_pow_smul_eq_zero_of_pow_smul_top_eq_bot {N : ℕ}
    (hN : S.I ^ N • (⊤ : Submodule S.A S.M) = ⊥) :
    ∃ n : ℕ, ∀ a ∈ S.I ^ n,
      ∀ x : (localCohomologyWithSupportInModuleFunctor.{u, v} S.A S.T i).obj
        (ModuleCat.of S.A S.M), a • x = 0 :=
  let ⟨_, _, h⟩ := exists_isEssentiallyConstantWith_of_pow_smul_top_eq_bot.{u, v} S i hN
  exists_pow_smul_eq_zero_of_isEssentiallyConstantWith S.A S.T S.I i _ h

/-- **Stacks Project, Tag 0EIE**, the limit consequence for a bootstrap situation in which `I`
acts nilpotently on `M`, with no hypothesis and in every degree: the quotient maps exhibit
`H^i_T(M)` as `lim H^i_T(M/IⁿM)`. -/
@[stacks 0EIE "the limit consequence H^i_T(M) = lim H^i_T(M/I^nM) for a bootstrap situation in
which I acts nilpotently on M, with no hypothesis and in every degree"]
def isLimit_of_pow_smul_top_eq_bot {N : ℕ}
    (hN : S.I ^ N • (⊤ : Submodule S.A S.M) = ⊥) :
    IsLimit (cone.{u, v} S i) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_isEssentiallyConstantWith_of_pow_smul_top_eq_bot.{u, v} S i hN))).isLimit

end Bootstrap

namespace Bootstrap

/-! ### The bootstrap situation at the closed point

When the ring of the situation is local and `T` is its closed point, the Mittag-Leffler
consequence holds with no hypothesis at all, and the essential-constancy assertion follows from
the identification `H^i_T(M) = lim H^i_T(M/IⁿM)` alone. The module universe is the ring
universe here, which is what the comparison of the two models of local cohomology asks for. -/

open Stacks.Algebraization

variable (S : BootstrapSituation.{u, u, w}) (i : ℤ)

/-- **Stacks Project, Tag 0EIE**, the Mittag-Leffler consequence for a bootstrap situation whose
ring is local and whose locus is the closed point, with no hypothesis. The terms
`H^i_T(M/IⁿM)` are then local cohomology at the maximal ideal of finite modules over a
Noetherian local ring, hence Artinian, and an inverse system of Artinian modules is
Mittag-Leffler. No degree restriction is needed either. -/
@[stacks 0EIE "the Mittag-Leffler consequence for a bootstrap situation whose ring is local and
whose locus T is the closed point, with no hypothesis and in every degree"]
theorem isMittagLeffler_of_eq_closedPoint [IsLocalRing S.A]
    (hT : S.T = {IsLocalRing.closedPoint S.A}) :
    IsMittagLefflerCategorical (tower.{u, u} S i) := by
  have h := isMittagLefflerCategorical_localCohomologyAdicTower_closedPoint S.A S.I i
    (ModuleCat.of S.A S.M)
  rwa [← hT] at h

/-- **Stacks Project, Tag 0EIE**, the essential-constancy assertion for a bootstrap situation
whose ring is local and whose locus is the closed point, from the identification
`H^i_T(M) = lim H^i_T(M/IⁿM)` alone.

That identification is the third of the four consequences above, and it is the one input of the
source's proof that the library does not supply here: the other two, the Mittag-Leffler
condition and the injectivity of `H^i_T(M) → H^i_T(M/IⁿM)` for `n ≫ 0`, are discharged by the
Artinianness of local cohomology at the maximal ideal. Composing with the four consequences
gives all of them from `hlim`.

Since `hlim` is itself one of the four consequences of Tag 0EIE, this implication carries no
registration of the tag. -/
theorem isEssentiallyConstantWith_of_eq_closedPoint_of_isLimit [IsLocalRing S.A]
    (hT : S.T = {IsLocalRing.closedPoint S.A}) (hlim : IsLimit (cone.{u, u} S i)) :
    ∃ (j : ℕᵒᵖ) (σ : (tower.{u, u} S i).obj j ⟶ (cone.{u, u} S i).pt),
      EssentiallyConstantPro.IsEssentiallyConstantWith
        (tower.{u, u} S i) (cone.{u, u} S i) j σ := by
  refine isEssentiallyConstantWith_localCohomologyAdicCone_of_isLimit.{u, u} S.A S.T S.I i
    (ModuleCat.of S.A S.M) hlim (isMittagLeffler_of_eq_closedPoint S i hT) ?_
  rw [hT]
  exact isArtinian_localCohomologyWithSupportIn_closedPoint S.A (ModuleCat.of S.A S.M) i

end Bootstrap

end Stacks.LocalCohomology

end
