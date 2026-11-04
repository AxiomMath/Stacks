module

public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
public import StacksFrontier.Topology.Sheaves.Modules.SquareZeroExtension
import StacksCore.Tactic.StacksAttribute

/-!
# The trivial square-zero thickening of a ringed space

For a ringed space `X` and an `𝒪_X`-module `𝒢`, the trivial square-zero extension
`𝒪_X ⋉ 𝒢` is the structure sheaf of a ringed space `X'` on the space of `X`, and the
projection `𝒪_X ⋉ 𝒢 ⟶ 𝒪_X` exhibits `X` as a first order thickening `i : X ⟶ X'` whose
kernel ideal `Ker(i^♯)` is `𝒢`. When `X` lies over a base `S`, the zero section
`𝒪_X ⟶ 𝒪_X ⋉ 𝒢` makes `X'` a space over `S` under which `i` is a morphism over `S`.

## Main definitions

* `Stacks.Deformation.TrivialSqZero.space`: the ringed space `X' = (X, 𝒪_X ⋉ 𝒢)`.
* `Stacks.Deformation.TrivialSqZero.thickening`: the morphism `i : X ⟶ X'`, the identity on
  the underlying space and the projection on structure sheaves.
* `Stacks.Deformation.TrivialSqZero.inrHom`: the inclusion `𝒢 ⟶ 𝒪_{X'}` of the ideal, as a
  morphism of `𝒪_{X'}`-modules out of `i_* 𝒢`.
* `Stacks.Deformation.TrivialSqZero.over`: the morphism `f' : X' ⟶ S` extending a morphism
  `f : X ⟶ S` through the zero section.

## Main results

* `Stacks.Deformation.TrivialSqZero.isFirstOrderThickening_thickening`: `i : X ⟶ X'` is a
  first order thickening of ringed spaces.
* `Stacks.Deformation.TrivialSqZero.apply_eq_zero_iff`: a local section of `𝒪_{X'}` is
  killed by `i^♯` exactly when it is the image of a unique local section of `𝒢`, which is
  the identification of `𝒢` with `Ker(i^♯)` on sections.
* `Stacks.Deformation.TrivialSqZero.isLimitInrKernelFork`: that identification as a limit,
  so that `Stacks.Deformation.TrivialSqZero.idealSheafIso` is an isomorphism
  `Ker(i^♯) ≅ i_* 𝒢` of `𝒪_{X'}`-modules.
* `Stacks.Deformation.TrivialSqZero.thickening_comp_over`: `i` is a morphism over `S`.

## No unrestricted `@[stacks 0GPZ]`

Tag 0GPZ asserts that the isomorphism classes of first order thickenings `i : X ⟶ X'` over
`S` with `Ker(i^♯) ≅ 𝒢` are canonically bijective to `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)`. Its proof has
exactly two inputs: the torsor statement of **Stacks 08UC**, that those classes are a
principal homogeneous space under that `Ext¹` once one of them exists, and the observation
that one does exist, namely `𝒢 ⊕ 𝒪_X`. This file supplies the second input, as data: the
thickening, the identification of its ideal with `𝒢`, and its morphism to `S`. It does not
prove the bijection, and no declaration here claims it — 08UC is not in the library, and a
torsor with no base point carries no bijection, so the two inputs are independent. Every
`@[stacks 0GPZ]` below therefore carries a restriction string naming what it is.

## Implementation notes

The underlying topological spaces of `X` and `X'` are equal and `i` is the identity on them,
which makes the comorphism of `i` literally the projection of the square-zero extension. All
three clauses of `IsThickening` then follow from properties of that projection alone: the
underlying map is an isomorphism because it is an identity, the structure-sheaf map is an
epimorphism of sheaves of modules because it is surjective on sections, and a section of its
kernel squares to zero over the open it is given on.

Modules on `X'` are compared with modules on `X` by pushforward along `i`, as in
`StacksFrontier/Topology/Sheaves/RingedSpace/Thickening.lean`, so the ideal of `i` is identified
with `i_* 𝒢` rather than with `𝒢`.

Two lemmas about the square-zero extension are restated here fully applied, as
`sqZeroPresheaf_map_inr` and `unit_map_apply`: the ones in
`StacksFrontier/Topology/Sheaves/Modules/SquareZeroExtension.lean` are stated for a module over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf 𝒪`, which matches
`structureSheafRing X` only after unfolding a semireducible definition, so
`rw` and `simp` cannot use them against a goal phrased in the latter.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.SheafOfModules (sqZeroPresheaf sqZeroSheaf sqZeroProj sqZeroInl
  moduleSections)
open AlgebraicGeometry.RingedSpaceThickening

universe u

attribute [local instance] Stacks.Smooth.moduleMulOpposite

namespace Stacks.Deformation.TrivialSqZero

variable (X : RingedSpace.{u, u})
  (G : SheafOfModules.{u} (structureSheafRing X))

/-- The ringed space whose space is that of `X` and whose structure sheaf is the trivial
square-zero extension `𝒪_X ⋉ 𝒢`. -/
def space : RingedSpace.{u, u} where
  carrier := X.carrier
  presheaf := (sqZeroSheaf X.sheaf G).obj
  IsSheaf := (sqZeroSheaf X.sheaf G).property

/-- The morphism `i : X ⟶ X'` which is the identity on the underlying space and the
projection `𝒪_X ⋉ 𝒢 ⟶ 𝒪_X` on structure sheaves. -/
def thickening : X ⟶ space X G :=
  ⟨{ base := 𝟙 X.carrier, c := (sqZeroProj X.sheaf G).hom }⟩

/-- The comorphism of `i : X ⟶ X'`, read on sections, is the first projection. -/
theorem structureSheafHom_thickening_app (U : (Opens (space X G).carrier)ᵒᵖ)
    (a : (structureSheafRing (space X G)).obj.obj U) :
    (structureSheafHom (thickening X G)).hom.app U a = TrivSqZeroExt.fst a :=
  rfl

/-- The comorphism of `i : X ⟶ X'` is surjective on sections, hence locally surjective. -/
theorem isLocallySurjective_structureSheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (space X G).carrier)
      (structureSheafHom (thickening X G)).hom :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ b => ⟨TrivSqZeroExt.inl b, rfl⟩

/-- An element of a trivial square-zero extension with vanishing first component is the image
of its second component. -/
theorem eq_inr_snd_of_fst_eq_zero {R M : Type*} [Zero R] (a : TrivSqZeroExt R M)
    (ha : TrivSqZeroExt.fst a = 0) : a = TrivSqZeroExt.inr (TrivSqZeroExt.snd a) :=
  TrivSqZeroExt.ext (by simp [ha]) (by simp)

/-- The product of two local sections of `𝒪_X ⋉ 𝒢` killed by `i^♯` vanishes. -/
theorem mul_eq_zero_of_apply_eq_zero (U : (Opens (space X G).carrier)ᵒᵖ)
    (a b : (structureSheafRing (space X G)).obj.obj U)
    (ha : (structureSheafHom (thickening X G)).hom.app U a = 0)
    (hb : (structureSheafHom (thickening X G)).hom.app U b = 0) : a * b = 0 := by
  let _ : Module ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) :=
    moduleSections (O := X.sheaf) (N := G) U
  have h : a = TrivSqZeroExt.inr (TrivSqZeroExt.snd a) := eq_inr_snd_of_fst_eq_zero a ha
  have h' : b = TrivSqZeroExt.inr (TrivSqZeroExt.snd b) := eq_inr_snd_of_fst_eq_zero b hb
  rw [h, h']
  exact TrivSqZeroExt.inr_mul_inr _ _ _

/-- `i : X ⟶ X'` is a thickening of ringed spaces. -/
theorem isThickening_thickening : IsThickening (thickening X G) := by
  refine ⟨?_, ?_, ?_⟩
  · show IsIso (𝟙 X.carrier)
    infer_instance
  · have h : Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (space X G).carrier)
        ((PresheafOfModules.toPresheaf _).map
          (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom (thickening X G))).val) :=
      ⟨fun s => (isLocallySurjective_structureSheafHom X G).imageSieve_mem s⟩
    have h2 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (thickening X G)))) := h
    exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance
  · intro U a ha x hx
    refine ⟨U, le_rfl, hx, 2, ?_⟩
    have hid : ((structureSheafRing (space X G)).obj.map
        (homOfLE (le_rfl (a := U))).op) a = a := by
      rw [show (homOfLE (le_rfl (a := U))).op = 𝟙 (op U) from rfl,
        CategoryTheory.Functor.map_id]
      rfl
    rw [hid, pow_two]
    exact mul_eq_zero_of_apply_eq_zero X G (op U) a a ha ha

/-- **`i : X ⟶ X'` is a first order thickening**: the square of the kernel ideal of `i^♯`
over an open is generated by products of sections killed by `i^♯`, all of which vanish. -/
@[stacks 0GPZ "the solution 𝒢 ⊕ 𝒪_X of the proof: it is a first order thickening of X; \
not the bijection with Ext¹, which needs the torsor statement of 08UC"]
theorem isFirstOrderThickening_thickening : IsFirstOrderThickening (thickening X G) := by
  refine ⟨isThickening_thickening X G, fun U => ?_⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one]
  exact le_antisymm (Ideal.mul_le.2 fun r hr s hs =>
    Ideal.mem_bot.2 (mul_eq_zero_of_apply_eq_zero X G (op U) r s hr hs)) bot_le

/-- **The ideal of `i : X ⟶ X'` is `𝒢`, on sections**: a local section of `𝒪_X ⋉ 𝒢` is killed
by `i^♯` exactly when it is the image of a unique local section of `𝒢`. -/
theorem apply_eq_zero_iff (U : (Opens (space X G).carrier)ᵒᵖ)
    (a : (structureSheafRing (space X G)).obj.obj U) :
    (structureSheafHom (thickening X G)).hom.app U a = 0 ↔
      ∃! n : G.val.obj U, a = TrivSqZeroExt.inr n := by
  let _ : Module ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) :=
    moduleSections (O := X.sheaf) (N := G) U
  constructor
  · intro ha
    refine ⟨TrivSqZeroExt.snd a, eq_inr_snd_of_fst_eq_zero a ha, fun m hm => ?_⟩
    rw [hm, TrivSqZeroExt.snd_inr]
  · rintro ⟨n, rfl, -⟩
    exact TrivSqZeroExt.fst_inr _ n

/-! ### The ideal as a module -/

/-- Restriction in `𝒪_X ⋉ 𝒢` of a section coming from `𝒢`. This is
`AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_fst` and `..._map_snd` at the spelling
`structureSheafRing X` of the ring of scalars of `𝒢`. -/
theorem sqZeroPresheaf_map_inr {U V : (Opens X.carrier)ᵒᵖ} (h : U ⟶ V) (m : G.val.obj U) :
    ((sqZeroPresheaf X.sheaf G).map h).hom (TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inr (G.val.map h m) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_fst (O := X.sheaf) (N := G) h
      (TrivSqZeroExt.inr m)).trans ?_
    rw [TrivSqZeroExt.fst_inr, map_zero]
    exact (TrivSqZeroExt.fst_inr _ _).symm
  · exact (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_snd (O := X.sheaf) (N := G) h
      (TrivSqZeroExt.inr m)).trans rfl

/-- Restriction in the unit module of `𝒪_{X'}` is restriction in `𝒪_X ⋉ 𝒢`. -/
theorem unit_map_apply {U V : (Opens (space X G).carrier)ᵒᵖ} (h : U ⟶ V)
    (a : (SheafOfModules.unit
      (structureSheafRing (space X G))).val.obj U) :
    (SheafOfModules.unit
        (structureSheafRing (space X G))).val.map h a =
      ((sqZeroPresheaf X.sheaf G).map h).hom a :=
  rfl

/-- Restriction in `i_* 𝒢` is restriction in `𝒢`. -/
theorem pushforward_map_apply {U V : (Opens (space X G).carrier)ᵒᵖ} (h : U ⟶ V)
    (n : ((modulePushforward (thickening X G)).obj G).val.obj U) :
    ((modulePushforward (thickening X G)).obj G).val.map h n =
      (show G.val.obj V from G.val.map h (show G.val.obj U from n)) :=
  rfl

/-- The inclusion of `𝒢` into `𝒪_X ⋉ 𝒢` over one open, as a map of `𝒪_{X'}`-modules. -/
def inrApp (U : (Opens (space X G).carrier)ᵒᵖ) :
    ((modulePushforward (thickening X G)).obj G).val.obj U ⟶
      (SheafOfModules.unit
        (structureSheafRing (space X G))).val.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun n => TrivSqZeroExt.inr (show G.val.obj U from n)
      map_add' := fun n m => TrivSqZeroExt.inr_add _ _ _
      map_smul' := by
        intro r n
        let _ : Module ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) :=
          moduleSections (O := X.sheaf) (N := G) U
        have h1 : (show ↥(G.val.obj U) from r • n) =
            TrivSqZeroExt.fst r • (show ↥(G.val.obj U) from n) := rfl
        have key : ∀ (r' : TrivSqZeroExt ↥(X.sheaf.obj.obj U) ↥(G.val.obj U))
            (m : ↥(G.val.obj U)),
            TrivSqZeroExt.inr (TrivSqZeroExt.fst r' • m) = r' * TrivSqZeroExt.inr m := by
          intro r' m
          conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r']
          rw [add_mul, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.inr_mul_inr, add_zero]
        rw [h1]
        exact key r n }

/-- The inclusion `i_* 𝒢 ⟶ 𝒪_{X'}` of the ideal of the trivial square-zero thickening. -/
def inrHom :
    (modulePushforward (thickening X G)).obj G ⟶
      SheafOfModules.unit (structureSheafRing (space X G)) where
  val :=
    { app := inrApp X G
      naturality := by
        intro U V h
        ext n
        change TrivSqZeroExt.inr (G.val.map h (show G.val.obj U from n)) =
          ((sqZeroPresheaf X.sheaf G).map h).hom
            (TrivSqZeroExt.inr (show G.val.obj U from n))
        exact (sqZeroPresheaf_map_inr X G h _).symm }

/-- `inrHom` on sections is the inclusion of `𝒢` as the second summand. -/
theorem inrHom_app_apply (U : (Opens (space X G).carrier)ᵒᵖ)
    (n : ((modulePushforward (thickening X G)).obj G).val.obj U) :
    (inrHom X G).val.app U n = TrivSqZeroExt.inr (show G.val.obj U from n) :=
  rfl

section Kernel

/-- The structure-sheaf map of `i`, as a morphism of `𝒪_{X'}`-modules out of the unit. -/
abbrev structureMap :
    SheafOfModules.unit (structureSheafRing (space X G)) ⟶
      (modulePushforward (thickening X G)).obj
        (SheafOfModules.unit (structureSheafRing X)) :=
  SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (thickening X G))

/-- The structure-sheaf map of `i`, read on sections, is the first projection. -/
theorem structureMap_app_apply (U : (Opens (space X G).carrier)ᵒᵖ)
    (a : (SheafOfModules.unit
      (structureSheafRing (space X G))).val.obj U) :
    (structureMap X G).val.app U a = TrivSqZeroExt.fst a :=
  rfl

/-- The inclusion of `𝒢` lands in the kernel ideal of `i^♯`. -/
theorem inrHom_comp_structureMap : inrHom X G ≫ structureMap X G = 0 := by
  ext U n
  exact TrivSqZeroExt.fst_inr _ (show G.val.obj U from n)

/-- The second component of a product in a trivial square-zero extension, when the second
factor has vanishing first component. -/
theorem snd_mul_of_fst_eq_zero {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (r a : TrivSqZeroExt R M) (ha : TrivSqZeroExt.fst a = 0) :
    TrivSqZeroExt.snd (r * a) = TrivSqZeroExt.fst r • TrivSqZeroExt.snd a := by
  rw [TrivSqZeroExt.snd_mul, ha]
  simp

variable {W : SheafOfModules.{u} (structureSheafRing (space X G))}
  (k : W ⟶ SheafOfModules.unit (structureSheafRing (space X G)))

/-- A map into `𝒪_{X'}` whose composite with `i^♯` vanishes has sections with vanishing first
component. -/
theorem fst_apply_eq_zero (hk : k ≫ structureMap X G = 0)
    (U : (Opens (space X G).carrier)ᵒᵖ) (w : W.val.obj U) :
    TrivSqZeroExt.fst (k.val.app U w) = 0 :=
  congrArg (fun φ : W ⟶ (modulePushforward (thickening X G)).obj
    (SheafOfModules.unit (structureSheafRing X)) => φ.val.app U w) hk

/-- The factorization through `𝒢` of a map into `𝒪_{X'}` killed by `i^♯`, over one open: a
section with vanishing first component is its second component. -/
def liftApp (hk : k ≫ structureMap X G = 0) (U : (Opens (space X G).carrier)ᵒᵖ) :
    W.val.obj U ⟶ ((modulePushforward (thickening X G)).obj G).val.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun w => (show ((modulePushforward (thickening X G)).obj G).val.obj U from
        TrivSqZeroExt.snd (k.val.app U w))
      map_add' := by
        intro w w'
        rw [map_add]
        exact TrivSqZeroExt.snd_add _ _
      map_smul' := by
        intro r w
        let _ : Module ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) :=
          moduleSections (O := X.sheaf) (N := G) U
        have h1 : (k.val.app U) (r • w) = r • (k.val.app U) w := map_smul _ r w
        have h2 := snd_mul_of_fst_eq_zero (M := ↥(G.val.obj U))
          (show TrivSqZeroExt ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) from r)
          (show TrivSqZeroExt ↥(X.sheaf.obj.obj U) ↥(G.val.obj U) from (k.val.app U) w)
          (fst_apply_eq_zero X G k hk U w)
        rw [h1]
        exact h2 }

/-- Restriction in `𝒪_X ⋉ 𝒢` acts on second components by restriction in `𝒢`. This is
`AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_snd` at the spelling
`structureSheafRing X` of the ring of scalars of `𝒢`. -/
theorem sqZeroPresheaf_map_snd' {U V : (Opens X.carrier)ᵒᵖ} (h : U ⟶ V)
    (a : (sqZeroPresheaf X.sheaf G).obj U) :
    TrivSqZeroExt.snd (((sqZeroPresheaf X.sheaf G).map h).hom a) =
      G.val.map h (TrivSqZeroExt.snd a) :=
  (AlgebraicGeometry.SheafOfModules.sqZeroPresheaf_map_snd (O := X.sheaf) (N := G) h a).trans rfl

/-- The factorization through `𝒢` of a map into `𝒪_{X'}` killed by `i^♯`. -/
def liftHom (hk : k ≫ structureMap X G = 0) :
    W ⟶ (modulePushforward (thickening X G)).obj G where
  val :=
    { app := liftApp X G k hk
      naturality := by
        intro U V h
        ext w
        change TrivSqZeroExt.snd (k.val.app V (W.val.map h w)) =
          (show G.val.obj V from
            G.val.map h (TrivSqZeroExt.snd (k.val.app U w)))
        rw [PresheafOfModules.naturality_apply k.val h w, unit_map_apply]
        exact sqZeroPresheaf_map_snd' X G h _ }

/-- **The inclusion of `𝒢` into `𝒪_X ⋉ 𝒢` is a kernel of `i^♯`**: a map into `𝒪_{X'}` killed
by `i^♯` factors through `𝒢` by taking second components, and does so uniquely. -/
def isLimitInrKernelFork :
    IsLimit (KernelFork.ofι (inrHom X G) (inrHom_comp_structureMap X G)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => liftHom X G k hk)
    (fun {W'} k hk => by
      ext U w
      change TrivSqZeroExt.inr (TrivSqZeroExt.snd (k.val.app U w)) = k.val.app U w
      refine (TrivSqZeroExt.inl_fst_add_inr_snd_eq (k.val.app U w)).symm.trans ?_ |>.symm
      rw [fst_apply_eq_zero X G k hk U w]
      simp)
    (fun {W'} k hk m hm => by
      ext U w
      change m.val.app U w = TrivSqZeroExt.snd (k.val.app U w)
      have h : TrivSqZeroExt.inr (show G.val.obj U from m.val.app U w) = k.val.app U w :=
        congrArg (fun φ : W' ⟶ SheafOfModules.unit
          (structureSheafRing (space X G)) => φ.val.app U w) hm
      rw [← h, TrivSqZeroExt.snd_inr])

/-- **The ideal of the trivial square-zero thickening is `𝒢`**: the canonical isomorphism
`Ker(i^♯) ≅ i_* 𝒢` of `𝒪_{X'}`-modules coming from the kernel property of the inclusion. -/
@[stacks 0GPZ "the solution 𝒢 ⊕ 𝒪_X of the proof: the identification of 𝒢 with Ker(i^♯); \
not the bijection with Ext¹, which needs the torsor statement of 08UC"]
def idealSheafIso :
    AlgebraicGeometry.SheafOfModules.idealSheaf (thickening X G) ≅
      (modulePushforward (thickening X G)).obj G :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimitInrKernelFork X G)

end Kernel

/-! ### The thickening over a base -/

section Over

variable {X G}
variable {S : RingedSpace.{u, u}}

/-- The morphism `f' : X' ⟶ S` extending `f : X ⟶ S` through the zero section
`𝒪_X ⟶ 𝒪_X ⋉ 𝒢`. -/
def over (f : X ⟶ S) : space X G ⟶ S :=
  ⟨{ base := f.hom.base
     c := f.hom.c ≫
       Functor.whiskerLeft (Opens.map f.hom.base).op (sqZeroInl X.sheaf G).hom }⟩

/-- `i : X ⟶ X'` is a morphism over `S`. -/
@[stacks 0GPZ "the solution 𝒢 ⊕ 𝒪_X of the proof: the thickening is a thickening over S; \
not the bijection with Ext¹, which needs the torsor statement of 08UC"]
theorem thickening_comp_over (f : X ⟶ S) : thickening X G ≫ over (G := G) f = f :=
  InducedCategory.hom_ext rfl

end Over

end Stacks.Deformation.TrivialSqZero

end
