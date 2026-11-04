module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Bridge.Basic
public import StacksFrontier.Topology.Sheaves.EpiMono.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of pushforward along a closed immersion of ringed spaces

Let `i : Z ⟶ X` be a morphism of ringed spaces whose underlying continuous map is a closed
embedding and whose comorphism of structure sheaves `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective, and
let `𝓘 ⊆ 𝒪_X` be the kernel of `i^♯`. This file proves that an `𝒪_X`-module `𝓖` is a
pushforward from `Z` exactly when `𝓘𝓖 = 0`. This is the essential-image assertion of Stacks
Tag 08KS.

## Main definitions

* `Stacks.Tag08KS.kernelIdeal`: the sectionwise kernel of `i^♯`.
* `Stacks.Tag08KS.IsAnnihilatedByKernelIdeal`: the condition `𝓘𝓖 = 0`, expressed sectionwise.

## Main results

* `Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates`: **Stacks 08KS**,
  the essential image of `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is exactly the modules annihilated by
  the kernel ideal.

## Implementation notes

The equation `𝓘𝓖 = 0` is expressed sectionwise: over every open `U` of `X`, every section of
`𝓘` kills every section of `𝓖`. That is the natural statement, and it is also the one the
proof wants, since the comparison it builds is checked on stalks of sections.

Because `i_*` is fully faithful (`Stacks.Tag08KS.modulePushforward_fullyFaithful`), membership
in its essential image is equivalent to the unit of `i^* ⊣ i_*` being an isomorphism at `𝓖`
(`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`). So both directions reduce to
statements about that unit.

The forward direction is formal: a pushforward is annihilated by the kernel ideal because the
`𝒪_X`-action on `i_*F` is the `𝒪_Z`-action restricted along `i^♯`
(`ModuleCat.restrictScalars.smul_def`), and the unit, being an isomorphism, is injective on
sections.

The converse direction checks that the unit is an isomorphism stalkwise, in two cases.

Over a point `i z` of the image, the stalk of `i^♯` is surjective (local surjectivity is
surjectivity on stalks, and `TopCat.Presheaf.stalkPushforward` is an isomorphism because a
closed embedding is inducing) and its kernel annihilates the stalk of `𝓖` (same transport
applied to the sectionwise hypothesis, after shrinking the open so that the two germs are
represented by honest sections). The stalk of the pullback is `𝒪_{Z,z} ⊗_{𝒪_{X,iz}} 𝓖_{iz}`
(`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`), and the unit on stalks
becomes `m ↦ 1 ⊗ m`. That map is bijective for a *surjective* ring map whose kernel
annihilates the module: `A/I ⊗_A M ≅ M/IM` (`TensorProduct.quotTensorEquivQuotSMul`) and
`IM = 0`.

Over a point outside the image both stalks vanish: the stalk of `i_* 𝒪_Z` is terminal by
Stacks 00AE (`ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange`), hence a
subsingleton, so `1` maps to `0` and the annihilation hypothesis kills the whole stalk of `𝓖`;
the same tag kills the stalk of the pushforward of the pullback. Terminality is converted to
`Subsingleton` by hand in `CommRingCat` (evaluating polynomials at two elements) and in
`AddCommGrpCat` (via `AddCommGrpCat.uliftZMultiplesAddEquiv`), because a terminal object of a
concrete category is not automatically known to be a one-element one.

Stalkwise bijectivity of the underlying map of sheaves of abelian groups gives that the unit
is an isomorphism there (`TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`), and
`CategoryTheory.SheafOfModules.toSheaf` reflects isomorphisms.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08KS

/-- In a restriction of scalars, a section of the ring acting as zero annihilates everything:
the action is the original action composed with the map of rings.

Stated for abstract presheaves of rings on purpose. The geometric spelling of the same fact
has `RingedSpaceModuleAdjunction.modulePushforward` on the outside, which is a `def`, so the
module structure on its sections is not visible to `ModuleCat.restrictScalars.smul_def`
without unfolding it. -/
private lemma restrictScalars_smul_eq_zero {C : Type*} [Category C]
    {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R') (M' : PresheafOfModules.{u} R')
    (U : Cᵒᵖ) (a : R.obj U) (ha : (α.app U).hom a = 0)
    (m : ((PresheafOfModules.restrictScalars α).obj M').obj U) :
    a • m = 0 := by
  show a • (show (ModuleCat.restrictScalars (α.app U).hom).obj (M'.obj U) from m) = 0
  rw [ModuleCat.restrictScalars.smul_def, ha, zero_smul]
  rfl

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- The ideal `𝓘 ⊆ 𝒪_X` which is the kernel of the comorphism `𝒪_X ⟶ i_* 𝒪_Z`, evaluated on
an open subset of `X`. -/
noncomputable def kernelIdeal (U : Opens X) : Ideal (X.presheaf.obj (op U)) :=
  RingHom.ker (i.hom.c.app (op U)).hom

/-- An `𝒪_X`-module is annihilated by the kernel ideal of the comorphism of structure sheaves
if, on every open subset of `X`, each section of the kernel ideal acts as zero. -/
abbrev IsAnnihilatedByKernelIdeal (G : SheafOfModules.{u} (structureSheafRing X)) : Prop :=
  ∀ (U : Opens X) (a : (structureSheafRing X).obj.obj (op U)),
    a ∈ kernelIdeal i U → ∀ m : G.val.obj (op U), a • m = 0

/-- Every pushforward is annihilated by the kernel ideal: the `𝒪_X`-action on `i_* F` is the
`𝒪_Z`-action restricted along the comorphism, which sends the section to zero. -/
private lemma modulePushforward_annihilatedByKernelIdeal
    (F : SheafOfModules.{u} (structureSheafRing Z)) :
    IsAnnihilatedByKernelIdeal i ((modulePushforward i).obj F) := fun U a ha m =>
  restrictScalars_smul_eq_zero (structureSheafHom i).hom
    ((PresheafOfModules.pushforward₀ (opensMap i) (structureSheafRing Z).obj).obj F.val)
    (op U) a ha m

/-- For a surjective ring map `f : A → B` whose kernel annihilates an `A`-module `M`, the map
`m ↦ 1 ⊗ m : M → B ⊗_A M` is bijective.

Indeed `B ≅ A/I` with `I = ker f`, and `A/I ⊗_A M ≅ M/IM = M` since `IM = 0`. -/
private theorem oneTensor_bijective_of_surjective_and_annihilated
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [Module A M] [Algebra A B] (f : A →+* B)
    (hcompat : algebraMap A B = f) (hf : Function.Surjective f)
    (hkill : ∀ a ∈ RingHom.ker f, ∀ m : M, a • m = 0) :
    Function.Bijective (fun m : M => (1 : B) ⊗ₜ[A] m) := by
  let I : Ideal A := RingHom.ker f
  let _ : CommRing (A ⧸ I) := Ideal.Quotient.commRing I
  let _ : Algebra A (A ⧸ I) := Ideal.Quotient.algebra A
  have hbot : I • (⊤ : Submodule A M) = ⊥ :=
    eq_bot_iff.2 <| Submodule.smul_le.2 fun a ha m _ => by simpa using hkill a ha m
  let e₀ : A ⧸ I ≃+* B := RingHom.quotientKerEquivOfSurjective (f := f) hf
  have hcomm : ∀ a : A, e₀ (algebraMap A (A ⧸ I) a) = algebraMap A B a := fun a => by
    rw [Ideal.Quotient.algebraMap_eq, RingHom.quotientKerEquivOfSurjective_apply_mk, hcompat]
  let e : (A ⧸ I) ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := e₀) hcomm
  let q := TensorProduct.quotTensorEquivQuotSMul M I
  let q' := (I • (⊤ : Submodule A M)).quotEquivOfEqBot hbot
  let tEquiv := q.trans q'
  let E := (e.toLinearEquiv.rTensor M).symm.trans tEquiv
  have hE (m : M) : E (1 ⊗ₜ[A] m) = m := by
    simp [E, tEquiv, q, q', e]
  exact ⟨fun m n h => by simpa [hE] using congrArg E h,
    fun m => ⟨E m, E.injective (by simp [hE])⟩⟩

/-- A map `ηst` that becomes a bijection `ι` after an injective comparison `κ` is a bijection.

Deliberately free of every typeclass: all four of `M`, `N`, `T`, and the maps are bare types
and functions. The call site instantiates `M` and `T` at the stalk of a sheaf of modules and at
a tensor product over stalks of structure sheaves, where no module instance is *findable* — the
structure sheaf is reached through `structureSheafRing`, a `def`, which
instance search will not unfold. A statement with no instances to find cannot fail that way:
the module structures travel inside the types of `ι`, `hι` and `κ`. -/
private theorem bijective_of_comparison {M N T : Type*}
    (κ : N → T) (hκ : Function.Injective κ)
    (ι : M → T) (hι : Function.Bijective ι)
    (ηst : M → N) (hformula : ∀ m : M, κ (ηst m) = ι m) :
    Function.Bijective ηst := by
  have hcomp : Function.Bijective (fun m : M => κ (ηst m)) := by
    rw [show (fun m : M => κ (ηst m)) = ι from funext hformula]
    exact hι
  refine ⟨fun m n h => hcomp.1 (congrArg κ h), fun y => ?_⟩
  obtain ⟨m, hm⟩ := hcomp.2 (κ y)
  exact ⟨m, hκ hm⟩

/-- The stalk pushforward comparison along an inducing map is bijective in a concrete category
whose forgetful functor reflects isomorphisms. -/
private lemma bijective_stalkPushforward_of_isInducing {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [(forget C).ReflectsIsomorphisms] [HasColimits C]
    {X Y : TopCat} {f : X ⟶ Y} (hf : Topology.IsInducing f) (F : X.Presheaf C) (x : X) :
    Function.Bijective (ConcreteCategory.hom (F.stalkPushforward C f x)) :=
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing C hf F x
  (ConcreteCategory.isIso_iff_bijective _).mp this

/-- The sectionwise annihilation hypothesis passes to stalks: a germ of `𝒪_X` killed by the
stalk of the comorphism kills every germ of `𝓖`.

The module is taken as a bare `PresheafOfModules` over `X.presheaf ⋙ forget₂ CommRingCat RingCat`
rather than as the underlying presheaf of a `SheafOfModules (structureSheafRing X)`. The two are
definitionally the same, but only the former type *displays* the structure presheaf as a
composite, which is what Mathlib's module structure on a stalk
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) is stated over — `structureSheafRing` is a
`def`, and instance search will not unfold it, so over the bundled spelling the `•` in this
statement has no instance at all. -/
private lemma stalk_annihilates_of_structureMap_eq_zero
    (Mp : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hMp : ∀ (U : Opens X) (a : X.presheaf.obj (op U)),
      a ∈ kernelIdeal i U → ∀ m : Mp.obj (op U), a • m = 0) (x : X) :
    ∀ a : X.presheaf.stalk x,
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map i.hom.c a = 0 →
        ∀ m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mp.presheaf x,
          a • m = 0 := by
  intro a ha m
  obtain ⟨U, hxU, aU, haU⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, mV, hmV⟩ := TopCat.Presheaf.exists_germ_eq Mp.presheaf m
  let U₀ := U ⊓ V
  have hxU₀ : x ∈ U₀ := ⟨hxU, hxV⟩
  let a₀ := X.presheaf.map (homOfLE (inf_le_left : U₀ ≤ U)).op aU
  let m₀ := Mp.presheaf.map (homOfLE (inf_le_right : U₀ ≤ V)).op mV
  have ha₀ : X.presheaf.germ U₀ x hxU₀ a₀ = a := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact haU
  have hm₀ : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Mp.presheaf U₀ x hxU₀ m₀ = m := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact hmV
  let q := (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj Z.presheaf
  let q₀ := (i.hom.c.app (op U₀)).hom a₀
  have hq₀ : q.germ U₀ x hxU₀ q₀ = 0 := by
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U₀ x hxU₀ i.hom.c a₀, ha₀]
    exact ha
  obtain ⟨W, hxW, iWU₀, iU₀top, hqzero⟩ :=
    q.germ_eq x hxU₀ (by trivial) q₀ 0 (by simpa using hq₀)
  let aW := X.presheaf.map iWU₀.op a₀
  let mW := Mp.presheaf.map iWU₀.op m₀
  have hxW' : x ∈ W := hxW
  have haW : X.presheaf.germ W x hxW' aW = a := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha₀
  have hmW : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Mp.presheaf W x hxW' mW = m := by
    rw [TopCat.Presheaf.germ_res_apply]
    exact hm₀
  have hmapW : (i.hom.c.app (op W)).hom aW = 0 := by
    have heq : (i.hom.c.app (op W)).hom aW = (q.map iWU₀.op).hom q₀ := by
      show ((X.presheaf.map iWU₀.op ≫ i.hom.c.app (op W)).hom) a₀ =
        ((i.hom.c.app (op U₀) ≫ q.map iWU₀.op).hom) a₀
      rw [i.hom.c.naturality iWU₀.op]
    exact heq.trans (by simpa using hqzero)
  have hkill := hMp W aW hmapW mW
  have hsmul := PresheafOfModules.germ_smul (R := X.presheaf) Mp x W hxW' aW mW
  rw [hkill, hmW, haW] at hsmul
  exact ((map_zero _).symm.trans hsmul).symm

/-- The kernel of the stalk map of local rings annihilates the stalk of `𝓖`.

The stalk of the comorphism and `PresheafedSpace.Hom.stalkMap` differ by the comparison
`TopCat.Presheaf.stalkPushforward`, which is an isomorphism for an inducing map. -/
private lemma kernel_stalk_annihilates
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (Mp : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hMp : ∀ (U : Opens X) (a : X.presheaf.obj (op U)),
      a ∈ kernelIdeal i U → ∀ m : Mp.obj (op U), a • m = 0) (z : Z) :
    ∀ a : X.presheaf.stalk (i.hom.base z),
      a ∈ RingHom.ker (i.hom.stalkMap z).hom →
        ∀ m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mp.presheaf (i.hom.base z),
          a • m = 0 := by
  intro a ha m
  have hc : (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (i.hom.base z)).map i.hom.c a = 0 := by
    have hinj := (bijective_stalkPushforward_of_isInducing (C := CommRingCat.{u})
      hi.isInducing Z.presheaf z).1
    have h0 : ConcreteCategory.hom (Z.presheaf.stalkPushforward CommRingCat.{u} i.hom.base z)
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (i.hom.base z)).map i.hom.c a) = 0 := ha
    exact hinj (h0.trans (map_zero _).symm)
  exact stalk_annihilates_of_structureMap_eq_zero i Mp hMp (i.hom.base z) a hc m

/-- The stalk map of local rings is surjective: local surjectivity of the comorphism is
surjectivity on stalks, and the pushforward comparison is an isomorphism. -/
private lemma structureMap_stalk_surjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c) (z : Z) :
    Function.Surjective (i.hom.stalkMap z).hom := by
  exact (bijective_stalkPushforward_of_isInducing (C := CommRingCat.{u})
    hi.isInducing Z.presheaf z).2.comp
    ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks i.hom.c).mp hs (i.hom.base z))

/-- If the stalk of the comorphism kills `1`, the whole stalk of `Mp` vanishes.

Phrased with a conclusion that mentions no `•`, so that instantiating `Mp` at `G.val` cannot
run into the missing module instance. -/
private lemma stalk_eq_zero_of_one_structureMap_eq_zero
    (Mp : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hMp : ∀ (U : Opens X) (a : X.presheaf.obj (op U)),
      a ∈ kernelIdeal i U → ∀ m : Mp.obj (op U), a • m = 0) (x : X)
    (h1 : (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map i.hom.c
      (1 : X.presheaf.stalk x) = 0)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mp.presheaf x) :
    m = 0 := by
  rw [← one_smul (X.presheaf.stalk x) m]
  exact stalk_annihilates_of_structureMap_eq_zero i Mp hMp x 1 h1 m

/-- **The local form of the essential-image criterion.** Over a point of the image, extension of
scalars `m ↦ 1 ⊗ m` from the stalk of `Mp` to its base change along the stalk map of structure
sheaves is bijective.

The stalk map is surjective because the comorphism is locally surjective, and its kernel
annihilates the stalk because the kernel ideal annihilates the sections. Phrased over a bare
`PresheafOfModules` so that every module instance in the statement is found by search; a
caller instantiates `Mp` at the underlying presheaf of a sheaf of modules, and the instances in
the result are then the very ones
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` uses. -/
private lemma oneTensor_stalk_bijective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c)
    (Mp : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (hMp : ∀ (U : Opens X) (a : X.presheaf.obj (op U)),
      a ∈ kernelIdeal i U → ∀ m : Mp.obj (op U), a • m = 0) (z : Z) :
    letI : Algebra (X.presheaf.stalk (i.hom.base z)) (Z.presheaf.stalk z) :=
      (i.hom.stalkMap z).hom.toAlgebra
    Function.Bijective
      (fun m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mp.presheaf (i.hom.base z) =>
        (1 : Z.presheaf.stalk z) ⊗ₜ[X.presheaf.stalk (i.hom.base z)] m) :=
  let : Algebra (X.presheaf.stalk (i.hom.base z)) (Z.presheaf.stalk z) :=
    (i.hom.stalkMap z).hom.toAlgebra
  oneTensor_bijective_of_surjective_and_annihilated (i.hom.stalkMap z).hom rfl
    (structureMap_stalk_surjective i hi hs z) (kernel_stalk_annihilates i hi Mp hMp z)

/-- A terminal object of `CommRingCat` is a subsingleton: two elements are separated by
evaluating polynomials, and the two evaluation maps out of a polynomial ring agree. -/
private lemma subsingleton_of_isTerminal_commRingCat {R : CommRingCat.{u}}
    (hR : IsTerminal R) : Subsingleton R := by
  refine ⟨fun a b => ?_⟩
  let P := Polynomial (↑R)
  let f : CommRingCat.of P ⟶ R := CommRingCat.ofHom (Polynomial.evalRingHom a)
  let g : CommRingCat.of P ⟶ R := CommRingCat.ofHom (Polynomial.evalRingHom b)
  have hX := congrArg (fun k => k.hom Polynomial.X) (hR.hom_ext f g)
  change Polynomial.X.eval a = Polynomial.X.eval b at hX
  simpa using hX

/-- A terminal object of `AddCommGrpCat` is a subsingleton: the forgetful functor is
corepresented by `ULift ℤ`. -/
private lemma subsingleton_of_isTerminal_addCommGrpCat {G : AddCommGrpCat.{u}}
    (hG : IsTerminal G) : Subsingleton G :=
  let e := AddCommGrpCat.uliftZMultiplesAddEquiv G
  ⟨fun a b => e.symm.injective (hG.hom_ext (e.symm a) (e.symm b))⟩

/-- Over a point of the image, the unit of `i^* ⊣ i_*` is bijective on stalks.

The stalk of the pullback is `𝒪_{Z,z} ⊗_{𝒪_{X,iz}} 𝓖_{iz}` and the unit becomes `m ↦ 1 ⊗ m`,
which is bijective because the stalk map is surjective with annihilating kernel. -/
private lemma modulePullback_unit_stalk_bijective_at_image
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (hG : IsAnnihilatedByKernelIdeal i G) (z : Z) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (i.hom.base z)).map
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
          ((modulePullbackPushforwardAdjunction i).unit.app G).val)) := by
  let adj := modulePullbackPushforwardAdjunction i
  let η := adj.unit.app G
  let ηab := (PresheafOfModules.toPresheaf (structureSheafRing X).obj).map η.val
  let ηst := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i.hom.base z)).map ηab
  let F := (modulePullback i).obj G
  let pullSt := TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base F.val.presheaf z
  obtain ⟨ePull, hePull⟩ := exists_modulePullbackStalkLinearEquiv i G z
  have hηgerm (V : Opens X) (hxV : i.hom.base z ∈ V) (s : G.val.obj (op V)) :
      ηst (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) G.val.presheaf V
          (i.hom.base z) hxV s) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj
            ((modulePullback i ⋙ modulePushforward i).obj G).val)
          V (i.hom.base z) hxV (η.val.app (op V) s) := by
    show ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i.hom.base z)).map ηab)
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj
            ((𝟭 (SheafOfModules (structureSheafRing X))).obj G).val)
          V (i.hom.base z) hxV s) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply V (i.hom.base z) hxV ηab s]
    simp only [ηab]
    have hsec := PresheafOfModules.toPresheaf_map_app_apply η.val (op V) s
    exact congrArg (fun t =>
      (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj
          ((modulePullback i ⋙ modulePushforward i).obj G).val) V
          (i.hom.base z) hxV)) t) hsec
  refine bijective_of_comparison (fun y => ePull (pullSt y))
    (ePull.injective.comp
      (bijective_stalkPushforward_of_isInducing (C := AddCommGrpCat.{u}) hi.isInducing _ _).1) _
    (oneTensor_stalk_bijective i hi hs G.val hG z) ηst ?_
  intro m
  obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
  refine (congrArg (fun t => ePull ((ConcreteCategory.hom pullSt) t)) (hηgerm V hxV s)).trans ?_
  show ePull (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base F.val.presheaf z
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i.hom.base).obj
        F.val.presheaf) V (i.hom.base z) hxV ((η.val.app (op V)) s))) = _
  refine (congrArg (fun t => ePull t) (TopCat.Presheaf.stalkPushforward_germ_apply
    AddCommGrpCat.{u} i.hom.base F.val.presheaf V z hxV (η.val.app (op V) s))).trans ?_
  exact hePull V hxV s

/-- Over a point outside the image, the unit of `i^* ⊣ i_*` is bijective on stalks because
both stalks vanish: the stalk of `i_* 𝒪_Z` is terminal by Stacks 00AE, so `1` is sent to `0`
and the annihilation hypothesis kills the stalk of `𝓖`, while the same tag kills the stalk of
the pushforward of the pullback. -/
private lemma modulePullback_unit_stalk_bijective_off_range
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (hG : IsAnnihilatedByKernelIdeal i G) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.hom.base)) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
          ((modulePullbackPushforwardAdjunction i).unit.app G).val)) := by
  let F := (modulePullback i).obj G
  let q := (TopCat.Presheaf.pushforward CommRingCat.{u} i.hom.base).obj Z.presheaf
  have hzeroStructure : (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map i.hom.c
      (1 : X.presheaf.stalk x) = 0 := by
    show (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map i.hom.c)) 1 = 0
    rw [map_one]
    show (1 : q.stalk x) = 0
    exact (subsingleton_of_isTerminal_commRingCat
      (ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
        i.hom.base Z.sheaf.property hi x hx)).elim _ _
  have hsourceZero := stalk_eq_zero_of_one_structureMap_eq_zero i G.val hG x hzeroStructure
  let Fsheaf := (SheafOfModules.toSheaf (structureSheafRing Z)).obj F
  have htermTgt := ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
    i.hom.base Fsheaf.property hi x hx
  have htargetSubEta : Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj
        ((modulePullback i ⋙ modulePushforward i).obj G).val)) := by
    let ePresheaf := (PresheafOfModules.pushforwardCompToPresheaf
      (φ := (structureSheafHom i).hom)).app F.val
    let eStalk := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso ePresheaf
    have eStalk' : ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i.hom.base).obj Fsheaf.obj)) ≅
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
          ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).obj
            ((modulePullback i ⋙ modulePushforward i).obj G).val)) := by
      simpa [TopCat.Presheaf.pushforward, Fsheaf, F, opensMap,
        PresheafOfModules.toPresheaf,
        RingedSpaceModuleAdjunction.modulePushforward, SheafOfModules.pushforward]
        using eStalk.symm
    exact subsingleton_of_isTerminal_addCommGrpCat (htermTgt.ofIso eStalk')
  exact ⟨fun a b _ => (hsourceZero a).trans (hsourceZero b).symm,
    fun b => ⟨0, htargetSubEta.elim _ _⟩⟩

/-- If the kernel ideal annihilates `𝓖` then the unit of `i^* ⊣ i_*` is an isomorphism at `𝓖`:
it is bijective on every stalk of the underlying sheaf of abelian groups, and
`SheafOfModules.toSheaf` reflects isomorphisms. -/
private lemma modulePullback_unit_isIso_of_annihilated
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c)
    (G : SheafOfModules.{u} (structureSheafRing X))
    (hG : IsAnnihilatedByKernelIdeal i G) :
    IsIso ((modulePullbackPushforwardAdjunction i).unit.app G) := by
  let η := (modulePullbackPushforwardAdjunction i).unit.app G
  let toAb := SheafOfModules.toSheaf (structureSheafRing X)
  have hstalk : ∀ x : X, Function.Bijective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toAb.map η).hom)) := by
    intro x
    by_cases hx : x ∈ Set.range (ConcreteCategory.hom i.hom.base)
    · obtain ⟨z, rfl⟩ := hx
      exact modulePullback_unit_stalk_bijective_at_image i hi hs G hG z
    · exact modulePullback_unit_stalk_bijective_off_range i hi G hG x hx
  have hstalkIso : ∀ x : X,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toAb.map η).hom) :=
    fun x => (ConcreteCategory.isIso_iff_bijective _).mpr (hstalk x)
  have hηsheaf : IsIso (toAb.map η) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (toAb.map η)
  exact isIso_of_reflects_iso η toAb

/-- **Stacks Project, Tag 08KS.** The essential image of pushforward along a morphism of ringed
spaces whose underlying continuous map is a closed embedding and whose comorphism of structure
sheaves is surjective consists exactly of the modules annihilated by the kernel ideal. -/
@[stacks 08KS "essential_image"]
theorem modulePushforward_essImage_iff_kernelIdeal_annihilates
    (hi : Topology.IsClosedEmbedding i.hom.base)
    (hs : TopCat.Presheaf.IsLocallySurjective i.hom.c)
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward i).essImage G ↔ IsAnnihilatedByKernelIdeal i G := by
  let adj := modulePullbackPushforwardAdjunction i
  have : (modulePushforward i).Full := modulePushforward_full i hi hs
  have : (modulePushforward i).Faithful := modulePushforward_faithful i hi hs
  rw [← adj.isIso_unit_app_iff_mem_essImage]
  constructor
  · intro h U a ha m
    let e := (adj.unit.app G).val.app (op U)
    have : IsIso e := by
      dsimp only [e]
      exact Functor.map_isIso
        (SheafOfModules.evaluation (structureSheafRing X) (op U)) (adj.unit.app G)
    have hinj : Function.Injective e :=
      ((ConcreteCategory.isIso_iff_bijective e).mp inferInstance).1
    have hmap : e (a • m) = 0 := by
      rw [map_smul]
      exact modulePushforward_annihilatedByKernelIdeal i ((modulePullback i).obj G) U a ha (e m)
    exact hinj (by simpa using hmap)
  · intro h
    exact modulePullback_unit_isIso_of_annihilated i hi hs G h

end Stacks.Tag08KS
