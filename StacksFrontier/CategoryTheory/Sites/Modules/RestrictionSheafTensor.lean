module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery

/-!
# Restriction of sheaves of modules commutes with sheafification and with the tensor product

Let `F : C ⥤ D` be continuous and cocontinuous for Grothendieck topologies `J` on `C` and `K` on
`D`, and let `R` be a sheaf of rings on `D`. *Restriction* along `F` is
`SheafOfModules.pushforward (𝟙 _)`, whose underlying presheaf is `F.op ⋙ -`: the sections of the
restriction over `U` are the sections of the original over `F(U)`. This file proves the two
compatibilities of that functor which a monoidal comparison needs.

The first is that restriction commutes with sheafification of presheaves of modules. This is
where cocontinuity enters: the restriction along `F.op` of the sheafification unit is locally
bijective (`CategoryTheory.Presheaf.isLocallyInjective_whisker` and
`isLocallySurjective_whisker` of Stacks 00XO), and the comparison map is the map through which it
factors.

The second is that restriction commutes with the sectionwise tensor product of presheaves of
modules. Over each object the two sides are the same module, because the sectionwise tensor
product is computed sectionwise; what is *not* free is the identification of the two presheaves of
modules, and the comparison is therefore constructed at the bilinear level rather than asserted.

## Main definitions

All in the namespace `Stacks.SheafOfModules.Restriction`.

* `sheafificationRestrictionHom` — the comparison map from "restrict, then sheafify" to
  "sheafify, then restrict", defined as the adjoint transpose of the restricted sheafification
  unit.
* `sheafificationRestrictionIso` — **restriction along a continuous and cocontinuous functor
  commutes with sheafification of presheaves of modules.**
* `tmulRestrict` and `restrictTmul` — the pure tensor of two sections over `F(W)`, read as a
  section over `W` of the sectionwise tensor product of the two restrictions, and as a section
  over `W` of the restriction of the sectionwise tensor product. These are the two elements the
  comparison is matched on, and they are definitions rather than notation for the reason given in
  the implementation notes.
* `presheafTensorRestrictionApp` and `presheafTensorRestrictionAppInv` — the comparison on
  sections and its inverse, both produced by `ModuleCat.MonoidalCategory.tensorLift` from the
  bilinear map `(a, b) ↦ a ⊗ b`.
* `presheafTensorRestrictionIsoApp` and `presheafTensorRestrictionObjIso` — the comparison on
  sections and on objects, as isomorphisms.
* `presheafTensorRestrictionIso` — **restriction commutes with the sectionwise tensor product of
  presheaves of modules**, along an arbitrary functor, as an isomorphism of bifunctors.
* `sheafTensorRestrictionIso` — **restriction along a continuous and cocontinuous functor
  commutes with the tensor product of sheaves of modules**, naturally in both arguments: the two
  previous isomorphisms whiskered together.
* `restrictModules` — restriction of *sheaves* of modules along `F`, with its target category
  written over the sheaf of rings of the restricted sheaf of commutative rings, which is the
  spelling `Stacks.SheafOfModules.Tensor.sheafTensor` is stated for.

## Main results

* `toSheafify_comp_sheafificationRestrictionHom` — on underlying presheaves of abelian groups the
  comparison is the map through which the restricted sheafification unit factors. This is the
  characterization the invertibility proof runs on.
* `sheafificationRestrictionHom_naturality` — the comparison is natural in the presheaf.
* `restrictPresheafModules_obj_obj`, `restrictPresheafModules_obj_map` and
  `restrictPresheafModules_map_app` — the three `rfl` head-symbol lemmas for restriction of
  presheaves of modules, through which everything about the tensor comparison is stated.
* `restrictTmul_restrict`, `tmulRestrict_restrict`,
  `restrictPresheafModules_map_restrictTmul` and `tensorHom_tmulRestrict` — the restriction maps
  and the functoriality of both sides, on the two named pure tensors. These four are the rewrite
  rules the naturality proofs run on.
* `restrictTmul_hom_ext` and `tmulRestrict_hom_ext` — a morphism out of either side is determined
  by its values on the pure tensors; `ModuleCat.MonoidalCategory.tensor_ext` with the two tensor
  factors supplied, so that no metavariable has to be solved against a restricted presheaf.
* `restrictModules_obj_obj` and `restrictModules_map_app` — the two `rfl` head-symbol lemmas for
  restriction of sheaves of modules, the sheaf-level companions of the three presheaf-level ones.
* `forget_comp_restrictPresheafModules` — restriction of sheaves of modules *is* restriction of
  the underlying presheaves of modules; an equality, not an isomorphism, because the change of
  scalars along the identity that `SheafOfModules.pushforward` carries is the identity.

## Implementation notes

Several declarations supply, as instances, that the identity between two definitionally equal but
differently spelled ring presheaves is locally bijective. Without them
`PresheafOfModules.sheafification` cannot be applied in the spelling that functor composition
forces, because instance search unfolds only reducible definitions: the restricted ring presheaf
arrives as `F.op ⋙ R.obj` from `PresheafOfModules.pushforward₀`, while
`SheafOfModules.pushforward` presents it as the underlying presheaf of
`F.sheafPushforwardContinuous RingCat J K` applied to `R`.  There is a third spelling, and
`isLocallyInjective_restrictionCommRingId` and its companion supply the instances for it: the
monoidal structure on presheaves of modules exists only over a ring presheaf of the shape
`O ⋙ forget₂ CommRingCat RingCat`, so the sectionwise tensor product on the restricted site
forces `(F.op ⋙ O.obj) ⋙ forget₂ _ _` where the pushforward produces
`F.op ⋙ (O.obj ⋙ forget₂ _ _)`.  Using `CategoryTheory.Sheaf.toRingCat` for the sheaf of rings
is what keeps this to one extra pair of instances: its underlying presheaf is syntactically
`O.obj ⋙ forget₂ _ _`, so the ring presheaf the tensor product is taken over and the one the
sheafification is taken over are the same term.

**Why the tensor comparison is constructed.** Its components are definitionally the identity, so
one is tempted to write `Iso.refl` and discharge only naturality. That does not elaborate: an
`Iso.refl` component asks the kernel to identify
`PresheafOfModules.pushforward₀` of `PresheafOfModules.Monoidal.tensorObj` with
`tensorObj` of two `pushforward₀`s as whole presheaves of modules — restriction maps, functoriality
proofs and all — and `whnf` does not finish. Four arrangements of that idea all
time out, including ascribing both composites to one written-out type and crossing the ring
spelling a second time; the identification is exactly what turning off the option
`backward.isDefEq.respectTransparency.types` buys, and no transparency option is used in this
file. What *is* cheap is the same identification one object at a time: the modules of
sections. So the comparison is built pointwise by `ModuleCat.MonoidalCategory.tensorLift` out of
`(a, b) ↦ a ⊗ b`, its two inverse laws are checked on pure tensors by
`ModuleCat.MonoidalCategory.tensor_ext`, and naturality — in the object of the site and in the two
presheaves of modules — is proved by rewriting with the four lemmas about `tmulRestrict` and
`restrictTmul` listed above.

Those two symbols exist for the reason `Stacks.PullbackTensor.germTmul` and `tmulGerm` do: a pure
tensor `a ⊗ₜ b` of sections has type `M(F(W)) ⊗ N(F(W))`, which is only definitionally and not
syntactically the sections of either side over `W`, so a rewrite rule mentioning it cannot be
applied by `rw` — building the motive requires checking the assignment at `implicit` transparency,
which fails. Giving each side a single head symbol makes all of those lemmas ordinary rewrite
rules. For the same reason the restriction lemmas are stated with `PresheafOfModules.restrictₛₗ`
rather than `PresheafOfModules.map`: the latter lands in
`ModuleCat.restrictScalars` of the target, and a rewrite whose right-hand side feeds such an
element to `restrictTmul` produces a goal that is not type-correct at `implicit` transparency, so
the next rewrite fails.

`restrictTmul` is *defined* as `tmulRestrict` rather than as a second `a ⊗ₜ b`. Writing the pure
tensor out again would produce a tensor product over `(O ⋙ forget₂ _ _).obj (F.op.obj W)`, whereas
the ambient `ModuleCat` has scalars `((F.op ⋙ O) ⋙ forget₂ _ _).obj W`; the two are the same ring,
but every bilinearity obligation then becomes a `SMulCommClass` problem between the two spellings
and no instance is found.

**What is not here.** `sheafTensorRestrictionIso` is stated for the composite "tensor the
underlying presheaves of modules sectionwise, then sheafify", which is what the construction
produces.  The development's own bifunctor for that composite is
`Stacks.SheafOfModules.Tensor.sheafTensor`, and the two differ in a way that is *not* a defeq
re-association: `Functor.uncurry` takes a morphism `(u, v)` of a product category to a whiskering
on the left followed by a whiskering on the right, whereas `MonoidalCategory.tensor` takes it to
`u ⊗ₘ v`, and the two agree only by `MonoidalCategory.tensorHom_def`, which is a theorem.  So
restating this isomorphism for `sheafTensor` needs a genuine comparison of the two bifunctors, and
the obvious `NatIso.ofComponents (fun _ => Iso.refl _)` does not close: its naturality goal
carries an identity whose object is spelled through one side's functor and whose composite is
spelled through the other's, so neither `Category.comp_id` nor `Category.id_comp` matches, and
chaining the whiskerings with `≪≫` instead asks `isDefEq` for
`restrictModules.prod restrictModules ⋙ forget.prod forget` against
`forget.prod forget ⋙ pushforward₀.prod pushforward₀` *inside* a composite that also contains the
sectionwise tensor product and the sheafification, which times out at `whnf` -- the composites are
equal (`forget_comp_restrictPresheafModules`) but the comparison is made at the wrong
bracketing, so the structural match fails and the unifier unfolds the tensor product.  Doing it
properly means explicit `Functor.associator`s and an `eqToIso` of
`forget_comp_restrictPresheafModules`, bracketed so that every structural match succeeds.

The tensor part of the file is stated for an arbitrary functor `F : C ⥤ D` and an arbitrary
presheaf of commutative rings `O : Dᵒᵖ ⥤ CommRingCat.{w}`: no topology, no sheaf condition and no
continuity hypothesis is involved. Its ring universe and module universe are both `w`, which is
forced — Mathlib's monoidal structure on presheaves of modules exists only for
`PresheafOfModules.{w}` over a ring presheaf of the shape `O ⋙ forget₂ CommRingCat RingCat` with
`O : Dᵒᵖ ⥤ CommRingCat.{w}`.

Nothing in the sheafification part fixes the ring universe or the module universe: the ring sheaf
lives in `RingCat.{r}` and the modules in `SheafOfModules.{w}`, with `r` and `w` independent of
each other and of the two site universes.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' r w

namespace Stacks.SheafOfModules.Restriction

variable {C : Type u} {D : Type v} [Category.{u'} C] [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-! ### Restriction and sheafification -/

/-- Viewed as a map from the restriction of the ring presheaf of `R` to the ring presheaf of the
restriction of `R`, the identity is locally injective: it is injective on sections. -/
instance isLocallyInjective_restrictionRingId
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r}) :
    Presheaf.IsLocallyInjective J
      (F₂ := ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R).obj)
      (𝟙 (F.op ⋙ R.obj)) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)

/-- Viewed as a map from the restriction of the ring presheaf of `R` to the ring presheaf of the
restriction of `R`, the identity is locally surjective: it is surjective on sections. -/
instance isLocallySurjective_restrictionRingId
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r}) :
    Presheaf.IsLocallySurjective J
      (G := ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R).obj)
      (𝟙 (F.op ⋙ R.obj)) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)

/-- The same statement in the spelling the sectionwise tensor product forces.  The monoidal
structure on presheaves of modules exists only over a ring presheaf of the shape
`O ⋙ forget₂ CommRingCat RingCat` with `O : Cᵒᵖ ⥤ CommRingCat`, so on the restricted site the
ring presheaf has to be written `(F.op ⋙ O.obj) ⋙ forget₂ _ _`, whereas
`PresheafOfModules.pushforward₀` and `isLocallyInjective_restrictionRingId` produce
`F.op ⋙ (O.obj ⋙ forget₂ _ _)`.  The two differ by the associativity of functor composition,
which instance search does not unfold, so this instance has to be supplied separately. -/
instance isLocallyInjective_restrictionCommRingId
    (F : C ⥤ D) [F.IsContinuous J K] [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (O : Sheaf K CommRingCat.{r}) :
    Presheaf.IsLocallyInjective J
      (F₂ := ((F.sheafPushforwardContinuous RingCat.{r} J K).obj
        (CategoryTheory.Sheaf.toRingCat K O)).obj)
      (𝟙 ((F.op ⋙ O.obj) ⋙ forget₂ CommRingCat.{r} RingCat.{r})) :=
  Presheaf.isLocallyInjective_of_injective _ _ (fun _ _ _ h => h)

/-- Companion of `isLocallyInjective_restrictionCommRingId`. -/
instance isLocallySurjective_restrictionCommRingId
    (F : C ⥤ D) [F.IsContinuous J K] [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (O : Sheaf K CommRingCat.{r}) :
    Presheaf.IsLocallySurjective J
      (G := ((F.sheafPushforwardContinuous RingCat.{r} J K).obj
        (CategoryTheory.Sheaf.toRingCat K O)).obj)
      (𝟙 ((F.op ⋙ O.obj) ⋙ forget₂ CommRingCat.{r} RingCat.{r})) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (fun _ x => ⟨x, rfl⟩)

section Sheafification

variable (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The comparison map from restricting a presheaf of modules along `F` and then sheafifying to
sheafifying and then restricting: the adjoint transpose of the restricted sheafification unit. -/
def sheafificationRestrictionHom (P : PresheafOfModules.{w} R.obj) :
    (PresheafOfModules.sheafification.{w}
        (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _)).obj
      ((PresheafOfModules.pushforward₀.{w} F R.obj).obj P) ⟶
    (SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _)).obj
      ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    ((PresheafOfModules.pushforward₀.{w} F R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))

/-- `sheafificationRestrictionHom` is by construction the adjoint transpose of the restricted
sheafification unit. -/
lemma sheafificationHomEquiv_sheafificationRestrictionHom (P : PresheafOfModules.{w} R.obj) :
    PresheafOfModules.sheafificationHomEquiv
        (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _)
        (sheafificationRestrictionHom (J := J) F R P) =
      (PresheafOfModules.pushforward₀.{w} F R.obj).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) :=
  Equiv.apply_symm_apply _ _

/-- On underlying presheaves of abelian groups, `sheafificationRestrictionHom` is the unique map
through which the restricted unit of sheafification factors. -/
lemma toSheafify_comp_sheafificationRestrictionHom (P : PresheafOfModules.{w} R.obj) :
    CategoryTheory.toSheafify J (F.op ⋙ P.presheaf) ≫
        ((SheafOfModules.toSheaf
          ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)).map
            (sheafificationRestrictionHom (J := J) F R P)).hom =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) :=
  ((PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def (𝟙 _)
      (sheafificationRestrictionHom (J := J) F R P)).symm.trans
    (congrArg (PresheafOfModules.toPresheaf _).map
      (sheafificationHomEquiv_sheafificationRestrictionHom F R P))).trans rfl

/-- `sheafificationRestrictionHom`, transposed through the sheafification adjunction. -/
lemma sheafificationAdjunction_homEquiv_sheafificationRestrictionHom
    (P : PresheafOfModules.{w} R.obj) :
    (PresheafOfModules.sheafificationAdjunction
        (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _)).homEquiv _ _
      (sheafificationRestrictionHom (J := J) F R P) =
      (PresheafOfModules.pushforward₀.{w} F R.obj).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) :=
  (PresheafOfModules.sheafificationAdjunction_homEquiv_apply (𝟙 _)
      (sheafificationRestrictionHom (J := J) F R P)).trans
    (sheafificationHomEquiv_sheafificationRestrictionHom F R P)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify K AddCommGrpCat] [K.WEqualsLocallyBijective AddCommGrpCat] in
/-- Restriction of presheaves of modules along `F` and the forgetful functor of sheaves of
modules commute with the restriction of sheaves of modules. -/
lemma pushforward₀_map_forget_map {M N : SheafOfModules.{w} R} (g : M ⟶ N) :
    (PresheafOfModules.pushforward₀.{w} F R.obj).map
        ((PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          ((SheafOfModules.forget.{w} R).map g)) =
      (PresheafOfModules.restrictScalars
          (𝟙 ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R).obj)).map
        ((SheafOfModules.forget.{w}
          ((F.sheafPushforwardContinuous RingCat.{r} J K).obj R)).map
            ((SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _)).map g)) :=
  rfl

/-- The comparison maps of `sheafificationRestrictionHom` are natural in the presheaf. -/
lemma sheafificationRestrictionHom_naturality {P Q : PresheafOfModules.{w} R.obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification.{w}
          (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _)).map
        ((PresheafOfModules.pushforward₀.{w} F R.obj).map f) ≫
      sheafificationRestrictionHom (J := J) F R Q =
    sheafificationRestrictionHom (J := J) F R P ≫
      (SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _)).map
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f) := by
  refine ((PresheafOfModules.sheafificationAdjunction
    (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _)).homEquiv
      _ _).injective ?_
  refine ((Adjunction.homEquiv_naturality_left
      (PresheafOfModules.sheafificationAdjunction
        (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _))
      ((PresheafOfModules.pushforward₀.{w} F R.obj).map f)
      (sheafificationRestrictionHom (J := J) F R Q)).trans ?_).trans
    (Adjunction.homEquiv_naturality_right
      (PresheafOfModules.sheafificationAdjunction
        (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _))
      (sheafificationRestrictionHom (J := J) F R P)
      ((SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _)).map
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f))).symm
  rw [sheafificationAdjunction_homEquiv_sheafificationRestrictionHom,
    sheafificationAdjunction_homEquiv_sheafificationRestrictionHom]
  refine Eq.trans ((PresheafOfModules.pushforward₀.{w} F R.obj).map_comp f
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q)).symm ?_
  refine Eq.trans (congrArg (PresheafOfModules.pushforward₀.{w} F R.obj).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.naturality f)) ?_
  refine Eq.trans ((PresheafOfModules.pushforward₀.{w} F R.obj).map_comp _ _) ?_
  exact congrArg (fun k => (PresheafOfModules.pushforward₀.{w} F R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) ≫ k)
    (pushforward₀_map_forget_map (J := J) F R
      ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).map f))

variable [F.IsCocontinuous J K] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Restriction along a continuous and cocontinuous functor commutes with sheafification of
presheaves of modules, objectwise. -/
lemma sheafificationRestrictionHom_isIso (P : PresheafOfModules.{w} R.obj) :
    IsIso (sheafificationRestrictionHom (J := J) F R P) := by
  let R' := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R
  let G := SheafOfModules.toSheaf.{w} R'
  let α := G.map (sheafificationRestrictionHom (J := J) F R P)
  have hfac : CategoryTheory.toSheafify J (F.op ⋙ P.presheaf) ≫ α.hom =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) :=
    toSheafify_comp_sheafificationRestrictionHom F R P
  have hwi : Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (F.op ⋙ P.presheaf) ≫ α.hom) := by
    rw [hfac]; exact Presheaf.isLocallyInjective_whisker J K F _
  have hws : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (F.op ⋙ P.presheaf) ≫ α.hom) := by
    rw [hfac]; exact Presheaf.isLocallySurjective_whisker J K F _
  have : IsIso α := (Sheaf.isLocallyBijective_iff_isIso α).mp
    ⟨Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J (F.op ⋙ P.presheaf)) α.hom,
      (Presheaf.comp_isLocallySurjective_iff J
        (CategoryTheory.toSheafify J (F.op ⋙ P.presheaf)) α.hom).mp hws⟩
  exact isIso_of_reflects_iso (sheafificationRestrictionHom (J := J) F R P) G

/-- **Restriction along a continuous and cocontinuous functor commutes with sheafification of
presheaves of modules.** -/
def sheafificationRestrictionIso :
    PresheafOfModules.pushforward₀.{w} F R.obj ⋙
        PresheafOfModules.sheafification.{w}
          (R := (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) (𝟙 _) ≅
      PresheafOfModules.sheafification.{w} (𝟙 R.obj) ⋙
        SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _) :=
  NatIso.ofComponents
    (fun P => @asIso _ _ _ _ (sheafificationRestrictionHom (J := J) F R P)
      (sheafificationRestrictionHom_isIso F R P))
    (fun f => sheafificationRestrictionHom_naturality F R f)

end Sheafification

/-! ### Restriction and the sectionwise tensor product -/

section PresheafTensor

open MonoidalCategory PresheafOfModules

variable (F : C ⥤ D) (O : Dᵒᵖ ⥤ CommRingCat.{w})
  (M N : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- The sections over `W` of the restriction of a presheaf of modules are the sections of the
original over `F(W)`.

This and the next two lemmas are the head-symbol lemmas through which restriction of presheaves
of modules is used below.  They hold by `rfl`, and they are what keeps the restriction opaque:
every statement about the comparison with the sectionwise tensor product is then an ordinary
rewrite rule, and `whnf` is never asked to identify
`PresheafOfModules.pushforward₀` of a tensor product with the tensor product of two
`PresheafOfModules.pushforward₀`s -- a defeq problem on whole presheaves of modules, including
their restriction maps and the proofs that these are functorial. -/
lemma restrictPresheafModules_obj_obj (W : Cᵒᵖ) :
    ((pushforward₀OfCommRingCat.{w} F O).obj M).obj W = M.obj (F.op.obj W) := rfl

/-- The restriction maps of a restricted presheaf of modules are the restriction maps of the
original along the images of the arrows. -/
lemma restrictPresheafModules_obj_map {W W' : Cᵒᵖ} (g : W ⟶ W') (a : M.obj (F.op.obj W)) :
    ((pushforward₀OfCommRingCat.{w} F O).obj M).map g a = M.map (F.op.map g) a := rfl

variable {M N} in
/-- A restricted morphism of presheaves of modules is the original morphism read over `F(W)`. -/
lemma restrictPresheafModules_map_app (u : M ⟶ N) (W : Cᵒᵖ) :
    Hom.app ((pushforward₀OfCommRingCat.{w} F O).map u) W = Hom.app u (F.op.obj W) := rfl

/-- The pure tensor `a ⊗ b` of two sections over `F(W)`, read as a section over `W` of the
sectionwise tensor product of the two restrictions.

The spelling matters, exactly as for `Stacks.PullbackTensor.tmulGerm`: `a ⊗ₜ b` has type
`M(F(W)) ⊗ N(F(W))`, which is only definitionally and not syntactically the sections over `W` of
a tensor product of restrictions, so a rewrite rule whose left-hand side mentions it directly
cannot be applied by `rw`.  Through this single head symbol the lemmas below are ordinary rewrite
rules. -/
def tmulRestrict (W : Cᵒᵖ) (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)) :
    ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
      (pushforward₀OfCommRingCat.{w} F O).obj N).obj W :=
  a ⊗ₜ b

/-- The same pure tensor, read as a section over `W` of the restriction of the sectionwise tensor
product `M ⊗ N`.  This is the counterpart of
`Stacks.SheafOfModules.Restriction.tmulRestrict` on the other side of the comparison, and it is a
definition for the same reason.

That it can be *defined* as the same element is the whole mathematical content of this section:
the sectionwise tensor product is computed sectionwise, so the sections over `W` of the
restriction of `M ⊗ N` and the sections over `W` of the tensor product of the restrictions are
the same module.  What is not free is the identification of the two *presheaves of modules*,
which is why the comparison below is constructed and not asserted.  Note also that the scalars of
the ambient `ModuleCat` are spelled `((F.op ⋙ O) ⋙ forget₂ _ _).obj W` on both sides here,
whereas writing `a ⊗ₜ b` out again would produce a tensor product over
`(O ⋙ forget₂ _ _).obj (F.op.obj W)` and make every bilinearity obligation a
`SMulCommClass` problem between two spellings of one ring. -/
def restrictTmul (W : Cᵒᵖ) (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)) :
    ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).obj W :=
  tmulRestrict F O M N W a b

/-- The restriction maps of the restriction of the sectionwise tensor product, on a pure
tensor. -/
lemma restrictTmul_restrict {W W' : Cᵒᵖ} (g : W ⟶ W') (a : M.obj (F.op.obj W))
    (b : N.obj (F.op.obj W)) :
    ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).map g (restrictTmul F O M N W a b) =
      restrictTmul F O M N W' (M.restrictₛₗ (F.op.map g) a) (N.restrictₛₗ (F.op.map g) b) := rfl

/-- The restriction maps of the sectionwise tensor product of the two restrictions, on a pure
tensor of sections. -/
lemma tmulRestrict_restrict {W W' : Cᵒᵖ} (g : W ⟶ W') (a : M.obj (F.op.obj W))
    (b : N.obj (F.op.obj W)) :
    ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
        (pushforward₀OfCommRingCat.{w} F O).obj N).map g (tmulRestrict F O M N W a b) =
      tmulRestrict F O M N W' (M.restrictₛₗ (F.op.map g) a) (N.restrictₛₗ (F.op.map g) b) := rfl

/-- A morphism out of the sections over `W` of the restriction of the sectionwise tensor product
is determined by its values on the pure tensors. -/
lemma restrictTmul_hom_ext {W : Cᵒᵖ}
    {P : ModuleCat.{w} ↑(((F.op ⋙ O) ⋙ forget₂ CommRingCat RingCat).obj W)}
    {x y : ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).obj W ⟶ P}
    (h : ∀ (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)),
      x (restrictTmul F O M N W a b) = y (restrictTmul F O M N W a b)) : x = y :=
  ModuleCat.MonoidalCategory.tensor_ext
    (M₁ := ((pushforward₀OfCommRingCat.{w} F O).obj M).obj W)
    (M₂ := ((pushforward₀OfCommRingCat.{w} F O).obj N).obj W) h

/-- A morphism out of the sections over `W` of the sectionwise tensor product of the two
restrictions is determined by its values on the pure tensors. -/
lemma tmulRestrict_hom_ext {W : Cᵒᵖ}
    {P : ModuleCat.{w} ↑(((F.op ⋙ O) ⋙ forget₂ CommRingCat RingCat).obj W)}
    {x y : ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
      (pushforward₀OfCommRingCat.{w} F O).obj N).obj W ⟶ P}
    (h : ∀ (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)),
      x (tmulRestrict F O M N W a b) = y (tmulRestrict F O M N W a b)) : x = y :=
  restrictTmul_hom_ext F O M N h

/-- The comparison on sections, from the restriction of the sectionwise tensor product to the
sectionwise tensor product of the two restrictions.  It is **constructed**, by
`ModuleCat.MonoidalCategory.tensorLift`, out of the bilinear map `(a, b) ↦ a ⊗ b`. -/
def presheafTensorRestrictionApp (W : Cᵒᵖ) :
    ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).obj W ⟶
      ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
        (pushforward₀OfCommRingCat.{w} F O).obj N).obj W :=
  ModuleCat.MonoidalCategory.tensorLift
    (M₁ := ((pushforward₀OfCommRingCat.{w} F O).obj M).obj W)
    (M₂ := ((pushforward₀OfCommRingCat.{w} F O).obj N).obj W)
    (fun a b => tmulRestrict F O M N W a b)
    (fun a a' b => TensorProduct.add_tmul a a' b)
    (fun r a b => TensorProduct.smul_tmul' r a b)
    (fun a b b' => TensorProduct.tmul_add a b b')
    (fun r a b => TensorProduct.tmul_smul r a b)

/-- The comparison on sections in the other direction, constructed out of the same bilinear
map. -/
def presheafTensorRestrictionAppInv (W : Cᵒᵖ) :
    ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
        (pushforward₀OfCommRingCat.{w} F O).obj N).obj W ⟶
      ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).obj W :=
  ModuleCat.MonoidalCategory.tensorLift
    (M₁ := ((pushforward₀OfCommRingCat.{w} F O).obj M).obj W)
    (M₂ := ((pushforward₀OfCommRingCat.{w} F O).obj N).obj W)
    (fun a b => restrictTmul F O M N W a b)
    (fun a a' b => TensorProduct.add_tmul a a' b)
    (fun r a b => TensorProduct.smul_tmul' r a b)
    (fun a b b' => TensorProduct.tmul_add a b b')
    (fun r a b => TensorProduct.tmul_smul r a b)

/-- `presheafTensorRestrictionApp` sends the restriction of `a ⊗ₜ b` to the tensor product of the
restrictions of `a` and `b`. -/
@[simp]
lemma presheafTensorRestrictionApp_restrictTmul (W : Cᵒᵖ) (a : M.obj (F.op.obj W))
    (b : N.obj (F.op.obj W)) :
    presheafTensorRestrictionApp F O M N W (restrictTmul F O M N W a b) =
      tmulRestrict F O M N W a b := rfl

/-- `presheafTensorRestrictionAppInv` sends the tensor product of the restrictions of `a` and `b`
to the restriction of `a ⊗ₜ b`. -/
@[simp]
lemma presheafTensorRestrictionAppInv_tmulRestrict (W : Cᵒᵖ) (a : M.obj (F.op.obj W))
    (b : N.obj (F.op.obj W)) :
    presheafTensorRestrictionAppInv F O M N W (tmulRestrict F O M N W a b) =
      restrictTmul F O M N W a b := rfl

/-- The comparison on sections is an isomorphism: both inverse laws are checked on the pure
tensors, by `ModuleCat.MonoidalCategory.tensor_ext`. -/
def presheafTensorRestrictionIsoApp (W : Cᵒᵖ) :
    ((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).obj W ≅
      ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
        (pushforward₀OfCommRingCat.{w} F O).obj N).obj W where
  hom := presheafTensorRestrictionApp F O M N W
  inv := presheafTensorRestrictionAppInv F O M N W
  hom_inv_id := restrictTmul_hom_ext F O M N fun a b => by
    change presheafTensorRestrictionAppInv F O M N W
        (presheafTensorRestrictionApp F O M N W (restrictTmul F O M N W a b)) =
      restrictTmul F O M N W a b
    rw [presheafTensorRestrictionApp_restrictTmul,
      presheafTensorRestrictionAppInv_tmulRestrict]
  inv_hom_id := tmulRestrict_hom_ext F O M N fun a b => by
    change presheafTensorRestrictionApp F O M N W
        (presheafTensorRestrictionAppInv F O M N W (tmulRestrict F O M N W a b)) =
      tmulRestrict F O M N W a b
    rw [presheafTensorRestrictionAppInv_tmulRestrict,
      presheafTensorRestrictionApp_restrictTmul]

/-- **Restriction commutes with the sectionwise tensor product of presheaves of modules**, along
an arbitrary functor, on objects. -/
def presheafTensorRestrictionObjIso :
    (pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N) ≅
      (pushforward₀OfCommRingCat.{w} F O).obj M ⊗
        (pushforward₀OfCommRingCat.{w} F O).obj N :=
  PresheafOfModules.isoMk (presheafTensorRestrictionIsoApp F O M N)
    (fun {W W'} g => restrictTmul_hom_ext F O M N fun a b => by
      change presheafTensorRestrictionApp F O M N W'
          (((pushforward₀OfCommRingCat.{w} F O).obj (M ⊗ N)).map g
            (restrictTmul F O M N W a b)) =
        ((pushforward₀OfCommRingCat.{w} F O).obj M ⊗
            (pushforward₀OfCommRingCat.{w} F O).obj N).map g
          (presheafTensorRestrictionApp F O M N W (restrictTmul F O M N W a b))
      rw [restrictTmul_restrict, presheafTensorRestrictionApp_restrictTmul,
        presheafTensorRestrictionApp_restrictTmul, tmulRestrict_restrict])

/-- On sections over `W`, the forward map of `presheafTensorRestrictionObjIso` sends the
restriction of `a ⊗ₜ b` to the tensor product of the restrictions of `a` and `b`. -/
@[simp]
lemma presheafTensorRestrictionObjIso_hom_app_restrictTmul (W : Cᵒᵖ) (a : M.obj (F.op.obj W))
    (b : N.obj (F.op.obj W)) :
    Hom.app (presheafTensorRestrictionObjIso F O M N).hom W (restrictTmul F O M N W a b) =
      tmulRestrict F O M N W a b := rfl

section Functoriality

variable {M N} (M' N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- Restriction of the sectionwise tensor product of two morphisms, on a pure tensor. -/
lemma restrictPresheafModules_map_restrictTmul (u : M ⟶ M') (v : N ⟶ N') (W : Cᵒᵖ)
    (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)) :
    Hom.app ((pushforward₀OfCommRingCat.{w} F O).map (u ⊗ₘ v)) W
        (restrictTmul F O M N W a b) =
      restrictTmul F O M' N' W (Hom.app u (F.op.obj W) a) (Hom.app v (F.op.obj W) b) := rfl

/-- The sectionwise tensor product of two restricted morphisms, on a pure tensor. -/
lemma tensorHom_tmulRestrict (u : M ⟶ M') (v : N ⟶ N') (W : Cᵒᵖ)
    (a : M.obj (F.op.obj W)) (b : N.obj (F.op.obj W)) :
    Hom.app ((pushforward₀OfCommRingCat.{w} F O).map u ⊗ₘ
        (pushforward₀OfCommRingCat.{w} F O).map v) W (tmulRestrict F O M N W a b) =
      tmulRestrict F O M' N' W (Hom.app u (F.op.obj W) a) (Hom.app v (F.op.obj W) b) := rfl

end Functoriality

/-- **Restriction commutes with the sectionwise tensor product of presheaves of modules**, along
an arbitrary functor, as an isomorphism of bifunctors: naturality in both presheaves of modules
is part of the statement. -/
def presheafTensorRestrictionIso :
    MonoidalCategory.tensor (PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) ⋙
        pushforward₀OfCommRingCat.{w} F O ≅
      (pushforward₀OfCommRingCat.{w} F O).prod (pushforward₀OfCommRingCat.{w} F O) ⋙
        MonoidalCategory.tensor
          (PresheafOfModules.{w} ((F.op ⋙ O) ⋙ forget₂ CommRingCat RingCat)) :=
  NatIso.ofComponents (fun MN => presheafTensorRestrictionObjIso F O MN.1 MN.2)
    (fun {MN MN'} uv => PresheafOfModules.hom_ext fun W =>
      restrictTmul_hom_ext F O MN.1 MN.2 fun a b => by
        change Hom.app (presheafTensorRestrictionObjIso F O MN'.1 MN'.2).hom W
            (Hom.app ((pushforward₀OfCommRingCat.{w} F O).map (uv.1 ⊗ₘ uv.2)) W
              (restrictTmul F O MN.1 MN.2 W a b)) =
          Hom.app ((pushforward₀OfCommRingCat.{w} F O).map uv.1 ⊗ₘ
              (pushforward₀OfCommRingCat.{w} F O).map uv.2) W
            (Hom.app (presheafTensorRestrictionObjIso F O MN.1 MN.2).hom W
              (restrictTmul F O MN.1 MN.2 W a b))
        rw [restrictPresheafModules_map_restrictTmul,
          presheafTensorRestrictionObjIso_hom_app_restrictTmul,
          presheafTensorRestrictionObjIso_hom_app_restrictTmul, tensorHom_tmulRestrict])

end PresheafTensor

/-! ### Restriction and the tensor product of sheaves of modules -/

section SheafTensor

open MonoidalCategory PresheafOfModules CategoryTheory.Sheaf

variable (F : C ⥤ D) [F.IsContinuous J K] (O : Sheaf K CommRingCat.{w})
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [F.IsCocontinuous J K] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- **Restriction along a continuous and cocontinuous functor commutes with the tensor product of
sheaves of modules**, in the form the construction produces it: on underlying presheaves of
modules, tensor sectionwise and sheafify.

The two steps are `presheafTensorRestrictionIso` -- restriction commutes with the sectionwise
tensor product -- and `sheafificationRestrictionIso` -- restriction commutes with sheafification.
The sheaf of rings is `CategoryTheory.Sheaf.toRingCat`, whose underlying presheaf is
syntactically `O.obj ⋙ forget₂ CommRingCat RingCat`, so that the ring presheaf the sectionwise
tensor product is taken over and the one the sheafification is taken over are the same term. -/
def sheafTensorRestrictionIso :
    (pushforward₀OfCommRingCat.{w} F O.obj).prod (pushforward₀OfCommRingCat.{w} F O.obj) ⋙
        MonoidalCategory.tensor
            (PresheafOfModules.{w} ((F.op ⋙ O.obj) ⋙ forget₂ CommRingCat RingCat)) ⋙
          PresheafOfModules.sheafification.{w}
            (R := (F.sheafPushforwardContinuous RingCat.{w} J K).obj (toRingCat K O)) (𝟙 _) ≅
      MonoidalCategory.tensor (PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat RingCat)) ⋙
        PresheafOfModules.sheafification.{w} (𝟙 (toRingCat K O).obj) ⋙
          SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _) :=
  (Functor.isoWhiskerRight (presheafTensorRestrictionIso F O.obj)
        (PresheafOfModules.sheafification.{w}
          (R := (F.sheafPushforwardContinuous RingCat.{w} J K).obj (toRingCat K O))
          (𝟙 _))).symm ≪≫
    Functor.isoWhiskerLeft
      (MonoidalCategory.tensor (PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat RingCat)))
      (sheafificationRestrictionIso F (toRingCat K O))

end SheafTensor

section SheafRestriction

open MonoidalCategory PresheafOfModules CategoryTheory.Sheaf Stacks.SheafOfModules.Tensor

variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K] (O : Sheaf K CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **Restriction of sheaves of modules along `F`**, with its target category written over the
sheaf of rings of the restricted sheaf of commutative rings.

This is `SheafOfModules.pushforward (𝟙 _)`, and the point of the declaration is the *type*:
`SheafOfModules.pushforward φ` has target `SheafOfModules S` for the source `S` of `φ`, and
`𝟙 _` forces `S` to be the term `(F.sheafPushforwardContinuous RingCat J K).obj (ringSheaf O)`,
which is not the spelling `Stacks.SheafOfModules.Tensor.sheafTensor` is stated for.  The two are
the same sheaf of rings, so the definition is accepted; writing it once is what lets a comparison
with `sheafTensor` be stated at all. -/
def restrictModules :
    SheafOfModules.{w} (ringSheaf O) ⥤
      SheafOfModules.{w}
        (ringSheaf ((F.sheafPushforwardContinuous CommRingCat.{w} J K).obj O)) :=
  SheafOfModules.pushforward.{w} (F := F) (J := J) (K := K) (𝟙 _)

omit [F.IsCocontinuous J K] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify K AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [J.HasSheafCompose (forget AddCommGrpCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sections over `W` of a restricted sheaf of modules are the sections of the original over
`F(W)`. -/
lemma restrictModules_obj_obj (M : SheafOfModules.{w} (ringSheaf O)) (W : Cᵒᵖ) :
    ((restrictModules (J := J) F O).obj M).val.obj W = M.val.obj (F.op.obj W) := rfl

omit [F.IsCocontinuous J K] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify K AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [J.HasSheafCompose (forget AddCommGrpCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A restricted morphism of sheaves of modules is the original morphism read over `F(W)`. -/
lemma restrictModules_map_app {M N : SheafOfModules.{w} (ringSheaf O)} (u : M ⟶ N) (W : Cᵒᵖ) :
    Hom.app ((restrictModules (J := J) F O).map u).val W = Hom.app u.val (F.op.obj W) := rfl

omit [F.IsCocontinuous J K] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify K AddCommGrpCat]
  [K.WEqualsLocallyBijective AddCommGrpCat] [J.HasSheafCompose (forget AddCommGrpCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Restriction of sheaves of modules is restriction of the underlying presheaves of modules.
The change of scalars along the identity that `SheafOfModules.pushforward` carries is the
identity, so the two composites are equal and not merely isomorphic. -/
lemma forget_comp_restrictPresheafModules :
    SheafOfModules.forget.{w} (ringSheaf O) ⋙ pushforward₀OfCommRingCat.{w} F O.obj =
      restrictModules (J := J) F O ⋙ SheafOfModules.forget.{w}
        (ringSheaf ((F.sheafPushforwardContinuous CommRingCat.{w} J K).obj O)) := rfl

end SheafRestriction

end Stacks.SheafOfModules.Restriction

end
