module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.Coequalizers

/-!
# Glueing an algebraic space back together from a proper modification

In the proper-modification situation of Stacks 0AGH -- a locally Noetherian algebraic space `X`
over `S`, a closed immersion `i : Z ⟶ X` with complementary open subspace `U`, and a proper
`f : X' ⟶ X` which is an isomorphism over `U` -- put `Y = X' ⨿ Z` and let `g : Y ⟶ X` be the
morphism which is `f` on `X'` and `i` on `Z`. The kernel pair `R = Y ×_X Y` of `g` has a
coequalizer `X₁`, the morphism `X₁ ⟶ X` is a finite universal homeomorphism, and `Z ⟶ X` lifts
to `X₁`. Replacing `Z` by a system of larger closed subspaces -- in the source, the
infinitesimal neighbourhoods `Z_n` of `Z` in `X` -- produces one such coequalizer `X_n` for
each `n` and a tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X` over `X`.

## Main definitions

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.glueSource` is `Y = X' ⨿ Z` and
  `AlgebraicGeometry.Space.CoequalizerGlueSituation.glueMap` is `g : Y ⟶ X`;
  `AlgebraicGeometry.Space.CoequalizerGlueSituation.relation` is the kernel pair `R = Y ×_X Y`
  with its two projections `leftProjection` and `rightProjection`.
* `AlgebraicGeometry.Space.KernelPairCoequalizer` is a coequalizer of the kernel pair of a
  morphism, together with the induced morphism to the target.
* `AlgebraicGeometry.Space.ProperKernelPairCoequalizers` is the conclusion of **Stacks 0AGG**,
  carried as a hypothesis; see "What is carried" below.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem` is an increasing
  system of closed subspaces of `X` over which the construction is repeated, and
  `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem.towerMap` is
  **Stacks 0AGJ**, the morphism `X_n ⟶ X_{n+1}` of the tower.

## Main results

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.isSurjective_glueMap`: the morphism
  `g : X' ⨿ Z ⟶ X` is surjective. This is what lets the universal-homeomorphism clause of
  Stacks 0AGG apply, and it is proved here from the two geometric inputs of Stacks 0AGH: `U`
  is exactly the complement of `Z` on points, and `f` is an isomorphism over `U`.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.nonempty_glueCoequalizer`,
  `isFinite_glueCoequalizer_toTarget`, `universalHomeomorphism_glueCoequalizer_toTarget`,
  `glueCoequalizer_closedSubspace_lift`: the clauses of **Stacks 0AGI**.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.ClosedSubspaceSystem.towerMap_comp_toTarget`:
  each morphism of the tower of **Stacks 0AGJ** is a morphism over `X`.

## What is carried, and what is proved

Stacks 0AGI reads, in full: "Existence of `X₁` and the fact that `X₁ → X` is a finite universal
homeomorphism is a special case of Lemma 0AGG." That lemma is therefore carried here as the one
named hypothesis `AlgebraicGeometry.Space.ProperKernelPairCoequalizers`, stated faithfully as
its own conclusion: existence of the coequalizer together with its five numbered clauses. The
reason it is carried rather than proved is not that its proof is long. That proof needs
`g_*𝒪_Y` and `h_*𝒪_R` to be coherent `𝒪_X`-algebras, which is Stacks 08AR, and 08AR is not
available: neither it nor its scheme-level counterpart Stacks 02O5 is proved anywhere, and the
inputs 02O5 itself needs — dévissage for coherent modules, Chow's lemma, the relative Leray
spectral sequence, and the vanishing of higher cohomology for relatively ample invertible
sheaves — are all absent, which is why
`StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic` proves coherence of the higher
direct images only under the stronger hypothesis that the morphism is finite. The higher direct
image itself is available: it is `(AlgebraicGeometry.Space.modulePushforward f).rightDerived n`,
as used in `StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange`. So
the hypothesis stands at a missing theorem with a long list of missing inputs, and it is one
named hypothesis which a later pass discharges by substitution.

Properness of `g : X' ⨿ Z ⟶ X` is likewise an argument rather than a conclusion. The source
obtains it silently from properness of `f` and the closed immersion `i`; the corresponding Lean
lemma, that `coprod.desc` of two proper morphisms is proper, exists for schemes as
`AlgebraicGeometry.isProper_coprodDesc` and has no analogue for algebraic spaces. It is carried
as the hypothesis `hproper` of the clauses that need it.

Surjectivity of `g` is *not* carried: it is proved, in
`AlgebraicGeometry.Space.CoequalizerGlueSituation.isSurjective_glueMap`, and so is the lift of
`Z`, and so is the whole tower of Stacks 0AGJ.

The remaining clause of Stacks 0AGI, that `X₁ ⟶ X` is an isomorphism over `U`, is not reached
here. The source gets it from the formation of `X₁` commuting with étale localization on `X`,
which is a property of the construction inside the proof of Stacks 0AGG and so is not visible
through that lemma's conclusion; deriving it needs, in addition, that `Z ×_X U` is an initial
algebraic space and that the coequalizer of the identity pair on `U` is `U`.

## Implementation notes

The coproduct `X' ⨿ Z` is taken in `AlgebraicGeometry.AlgebraicSpaces`, the category of
Stacks 02X2, where it exists unconditionally: the index type of a binary coproduct is
countable, so `AlgebraicGeometry.Space.hasColimitsOfShape_discrete_algebraicSpaces` applies.
The kernel pair is the fibre product of that category, which is computed in presheaves by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`.

A coequalizer is carried as the datum `AlgebraicGeometry.Space.KernelPairCoequalizer` rather
than as `CategoryTheory.Limits.coequalizer`, so that the clauses of Stacks 0AGG are stated
about an arbitrary such datum and the hypothesis has no dependency between its fields.

The system of closed subspaces is data. Identifying its members with the `n`th order
infinitesimal neighbourhoods of `Z` in `X` is a separate matter: the construction is
`AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood`, which takes a surjective étale
chart of `X` and a sheaf of ideals on that chart invariant under the relation it presents, and
that identification is not carried out here.

## References

* [Stacks Project, Tag 0AGI](https://stacks.math.columbia.edu/tag/0AGI)
* [Stacks Project, Tag 0AGJ](https://stacks.math.columbia.edu/tag/0AGJ)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 0AGH](https://stacks.math.columbia.edu/tag/0AGH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The source of the glueing and its morphism to the target -/

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-- The target `X` of the proper modification, as an object of the category of algebraic
spaces over `S`. -/
abbrev targetSpace : AlgebraicSpaces T.B T.S T.hS := ⟨T.X, T.hX⟩

/-- The source `X'` of the proper modification, as an object of the category of algebraic
spaces over `S`. -/
abbrev modificationSpace : AlgebraicSpaces T.B T.S T.hS := ⟨T.X', T.hX'⟩

/-- The closed subspace `Z`, as an object of the category of algebraic spaces over `S`. -/
abbrev closedSpace : AlgebraicSpaces T.B T.S T.hS := ⟨T.Z, T.hZ⟩

/-- The algebraic space `Y = X' ⨿ Z` which is glued back onto `X`. -/
abbrev glueSource : AlgebraicSpaces T.B T.S T.hS := T.modificationSpace ⨿ T.closedSpace

/-- The morphism `g : Y = X' ⨿ Z ⟶ X` which is the proper modification `f` on `X'` and the
closed immersion `i` on `Z`. -/
def glueMap : T.glueSource ⟶ T.targetSpace :=
  coprod.desc (ObjectProperty.homMk T.f) (ObjectProperty.homMk T.i)

@[simp]
theorem inl_glueMap :
    (coprod.inl : T.modificationSpace ⟶ T.glueSource) ≫ T.glueMap = ObjectProperty.homMk T.f := by
  rw [glueMap, coprod.inl_desc]

@[simp]
theorem inr_glueMap :
    (coprod.inr : T.closedSpace ⟶ T.glueSource) ≫ T.glueMap = ObjectProperty.homMk T.i := by
  rw [glueMap, coprod.inr_desc]

theorem inl_comp_glueMap :
    (coprod.inl : T.modificationSpace ⟶ T.glueSource).hom ≫ T.glueMap.hom = T.f :=
  congrArg (fun m : T.modificationSpace ⟶ T.targetSpace => m.hom) T.inl_glueMap

theorem inr_comp_glueMap :
    (coprod.inr : T.closedSpace ⟶ T.glueSource).hom ≫ T.glueMap.hom = T.i :=
  congrArg (fun m : T.closedSpace ⟶ T.targetSpace => m.hom) T.inr_glueMap

/-- The kernel pair `R = Y ×_X Y` of the glueing morphism. -/
abbrev relation : AlgebraicSpaces T.B T.S T.hS := pullback T.glueMap T.glueMap

/-- The projection `t : R ⟶ Y`. -/
abbrev leftProjection : T.relation ⟶ T.glueSource := pullback.fst T.glueMap T.glueMap

/-- The projection `s : R ⟶ Y`. -/
abbrev rightProjection : T.relation ⟶ T.glueSource := pullback.snd T.glueMap T.glueMap

theorem leftProjection_comp_glueMap :
    T.leftProjection ≫ T.glueMap = T.rightProjection ≫ T.glueMap :=
  pullback.condition

/-! ### Surjectivity of the glueing morphism -/

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_CoequalizerGlueing {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

/-- Every point of the complementary open subspace `U` is in the image of the proper
modification `f`, because `f` is an isomorphism over `U`. -/
theorem range_pointsMap_ι_subset_range_pointsMap_f :
    Set.range (pointsMap T.B T.S T.hS T.U.toFunctor T.U.ι) ⊆
      Set.range (pointsMap T.B T.S T.hS T.X' T.f) := by
  have hiso := T.f_iso_over_U
  have hc : pullback.fst T.f T.U.ι ≫ T.f = pullback.snd T.f T.U.ι ≫ T.U.ι :=
    pullback.condition
  have hU : T.U.ι = inv (pullback.snd T.f T.U.ι) ≫ pullback.fst T.f T.U.ι ≫ T.f := by
    rw [hc, IsIso.inv_hom_id_assoc]
  rw [hU, pointsMap_comp, pointsMap_comp]
  rintro x ⟨p, rfl⟩
  exact ⟨_, rfl⟩

/-- The morphism `g : X' ⨿ Z ⟶ X` is surjective: a point of `X` either lies in `Z`, where it
is hit by the closed immersion `i`, or in the complementary open `U`, where it is hit by the
proper modification `f` because `f` is an isomorphism over `U`. -/
theorem isSurjective_glueMap : IsSurjective T.B T.S T.hS T.glueMap.hom := by
  intro x
  by_cases hx : x ∈ Set.range (pointsMap T.B T.S T.hS T.Z T.i)
  · obtain ⟨z, hz⟩ := hx
    rw [← T.inr_comp_glueMap, pointsMap_comp] at hz
    exact ⟨_, hz⟩
  · have hxU : x ∈ Set.range (pointsMap T.B T.S T.hS T.U.toFunctor T.U.ι) := by
      rw [T.U_compl_Z]; exact hx
    obtain ⟨w, hw⟩ := T.range_pointsMap_ι_subset_range_pointsMap_f hxU
    rw [← T.inl_comp_glueMap, pointsMap_comp] at hw
    exact ⟨_, hw⟩

end CoequalizerGlueSituation

/-! ### Coequalizers of kernel pairs -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A coequalizer of the kernel pair of a morphism `g : Y ⟶ X` of algebraic spaces over `S`,
together with the morphism to `X` through which `g` factors. -/
structure KernelPairCoequalizer {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) where
  /-- The coequalizer. -/
  space : AlgebraicSpaces B S hS
  /-- The quotient morphism. -/
  π : Y ⟶ space
  /-- The induced morphism to the target of `g`. -/
  toTarget : space ⟶ X
  /-- The quotient morphism followed by the morphism to the target is `g`. -/
  fac : π ≫ toTarget = g
  /-- The quotient morphism identifies the two projections of the kernel pair. -/
  equalizes : pullback.fst g g ≫ π = pullback.snd g g ≫ π
  /-- The quotient morphism is a coequalizer of the two projections. -/
  isColimit : IsColimit (Cofork.ofπ π equalizes)

/-- The conclusion of **Stacks 0AGG**: for a proper morphism `g : Y ⟶ X` of algebraic spaces
over `S` with `X` locally Noetherian, the kernel pair of `g` has a coequalizer; the induced
morphism to `X` is finite and universally injective; the quotient morphism is proper and
surjective; and the morphism to `X` is a universal homeomorphism when `g` is surjective.

This is carried as a hypothesis because the proof of Stacks 0AGG rests on Stacks 08AR, whose
subject `R^i f_*𝓕` is not expressible for a morphism of algebraic spaces at the universe the
statement needs. -/
structure ProperKernelPairCoequalizers : Prop where
  /-- A coequalizer of the kernel pair exists. -/
  nonempty_coequalizer : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → Nonempty (KernelPairCoequalizer B S hS g)
  /-- Part (1): the morphism from the coequalizer to `X` is finite. -/
  isFinite_toTarget : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsFinite B S hS D.toTarget.hom
  /-- Part (2): the quotient morphism is proper. -/
  isProper_π : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsProper B S hS D.π.hom
  /-- Part (3): the quotient morphism is surjective. -/
  isSurjective_π : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsSurjective B S hS D.π.hom
  /-- Part (4): the morphism from the coequalizer to `X` is universally injective. -/
  universallyInjective_toTarget : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      UniversallyInjective B S hS D.toTarget.hom
  /-- Part (5): if `g` is surjective, the morphism from the coequalizer to `X` is a universal
  homeomorphism. -/
  universalHomeomorphism_toTarget : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → IsSurjective B S hS g.hom →
    ∀ D : KernelPairCoequalizer B S hS g,
      UniversalHomeomorphism B S hS D.toTarget.hom

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### Stacks 0AGI -/

/-- **Stacks 0AGI**, existence of the coequalizer `X₁` of `s, t : R ⟶ Y` in the category of
algebraic spaces over `S`, for `Y = X' ⨿ Z` and `R = Y ×_X Y`. -/
@[stacks 0AGI "existence of the coequalizer; this clause is Stacks 0AGG, carried as the \
hypothesis hAGG because 0AGG rests on 08AR, which the library does not have"]
theorem nonempty_glueCoequalizer
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hproper : IsProper T.B T.S T.hS T.glueMap.hom) :
    Nonempty (KernelPairCoequalizer T.B T.S T.hS T.glueMap) :=
  hAGG.nonempty_coequalizer T.glueMap T.locallyNoetherian hproper

/-- **Stacks 0AGI**, finiteness of `X₁ ⟶ X`. -/
@[stacks 0AGI "the morphism to X is finite; this clause is part (1) of Stacks 0AGG, carried as \
the hypothesis hAGG"]
theorem isFinite_glueCoequalizer_toTarget
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hproper : IsProper T.B T.S T.hS T.glueMap.hom)
    (D : KernelPairCoequalizer T.B T.S T.hS T.glueMap) :
    IsFinite T.B T.S T.hS D.toTarget.hom :=
  hAGG.isFinite_toTarget T.glueMap T.locallyNoetherian hproper D

/-- **Stacks 0AGI**, the morphism `X₁ ⟶ X` is a universal homeomorphism. The surjectivity of
`g` which part (5) of Stacks 0AGG asks for is supplied by
`AlgebraicGeometry.Space.CoequalizerGlueSituation.isSurjective_glueMap`. -/
@[stacks 0AGI "the morphism to X is a universal homeomorphism; part (5) of Stacks 0AGG is \
carried as the hypothesis hAGG, and its surjectivity input is proved here"]
theorem universalHomeomorphism_glueCoequalizer_toTarget
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hproper : IsProper T.B T.S T.hS T.glueMap.hom)
    (D : KernelPairCoequalizer T.B T.S T.hS T.glueMap) :
    UniversalHomeomorphism T.B T.S T.hS D.toTarget.hom :=
  hAGG.universalHomeomorphism_toTarget T.glueMap T.locallyNoetherian hproper
    T.isSurjective_glueMap D

/-- **Stacks 0AGI**, the closed immersion `Z ⟶ X` lifts to the coequalizer: the composition of
the coproduct inclusion of `Z` with the quotient morphism is a lift. This clause is proved
outright: it needs only that `Y ⟶ X₁ ⟶ X` is `g`, which is `g` on the summand `Z`. -/
@[stacks 0AGI "Z lifts to the coequalizer; proved here"]
theorem glueCoequalizer_closedSubspace_lift
    (D : KernelPairCoequalizer T.B T.S T.hS T.glueMap) :
    (coprod.inr ≫ D.π) ≫ D.toTarget = (ObjectProperty.homMk T.i : _ ⟶ T.targetSpace) := by
  rw [Category.assoc, D.fac, T.inr_glueMap]

/-! ### Stacks 0AGJ -/

/-- An increasing system of closed subspaces of `X` over `X`, over which the glueing
construction is repeated. In Stacks 0AGJ the members are the infinitesimal neighbourhoods
`Z_n` of `Z` in `X`. -/
structure ClosedSubspaceSystem where
  /-- The `n`th member of the system. -/
  space : ℕ → AlgebraicSpaces T.B T.S T.hS
  /-- The morphism of the `n`th member to `X`. -/
  toTarget : ∀ n, space n ⟶ T.targetSpace
  /-- The morphism of the `n`th member to `X` is a closed immersion. -/
  isClosedImmersion_toTarget : ∀ n, IsClosedImmersion T.B T.S T.hS (toTarget n).hom
  /-- The inclusion of the `n`th member into the next. -/
  step : ∀ n, space n ⟶ space (n + 1)
  /-- The inclusions are morphisms over `X`. -/
  step_comp_toTarget : ∀ n, step n ≫ toTarget (n + 1) = toTarget n

namespace ClosedSubspaceSystem

variable {T} (N : T.ClosedSubspaceSystem)

/-- The algebraic space `Y_n = X' ⨿ Z_n`. -/
abbrev glueSourceAt (n : ℕ) : AlgebraicSpaces T.B T.S T.hS :=
  T.modificationSpace ⨿ N.space n

/-- The morphism `g_n : Y_n ⟶ X`, which is `f` on `X'` and the inclusion on `Z_n`. -/
def glueMapAt (n : ℕ) : N.glueSourceAt n ⟶ T.targetSpace :=
  coprod.desc (ObjectProperty.homMk T.f) (N.toTarget n)

/-- The morphism `Y_n ⟶ Y_{n+1}` induced by the inclusion `Z_n ⟶ Z_{n+1}`. -/
def sourceStep (n : ℕ) : N.glueSourceAt n ⟶ N.glueSourceAt (n + 1) :=
  coprod.map (𝟙 T.modificationSpace) (N.step n)

@[simp]
theorem sourceStep_comp_glueMapAt (n : ℕ) :
    N.sourceStep n ≫ N.glueMapAt (n + 1) = N.glueMapAt n := by
  refine coprod.hom_ext ?_ ?_ <;>
    simp [sourceStep, glueMapAt, N.step_comp_toTarget]

/-- The morphism `R_n ⟶ R_{n+1}` of kernel pairs induced by `Y_n ⟶ Y_{n+1}`. -/
def relationStep (n : ℕ) :
    pullback (N.glueMapAt n) (N.glueMapAt n) ⟶
      pullback (N.glueMapAt (n + 1)) (N.glueMapAt (n + 1)) :=
  pullback.lift (pullback.fst _ _ ≫ N.sourceStep n) (pullback.snd _ _ ≫ N.sourceStep n)
    (by rw [Category.assoc, Category.assoc, N.sourceStep_comp_glueMapAt,
      pullback.condition])

@[simp]
theorem relationStep_comp_fst (n : ℕ) :
    N.relationStep n ≫ pullback.fst (N.glueMapAt (n + 1)) (N.glueMapAt (n + 1)) =
      pullback.fst (N.glueMapAt n) (N.glueMapAt n) ≫ N.sourceStep n :=
  pullback.lift_fst _ _ _

@[simp]
theorem relationStep_comp_snd (n : ℕ) :
    N.relationStep n ≫ pullback.snd (N.glueMapAt (n + 1)) (N.glueMapAt (n + 1)) =
      pullback.snd (N.glueMapAt n) (N.glueMapAt n) ≫ N.sourceStep n :=
  pullback.lift_snd _ _ _

variable (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (N.glueMapAt n))

/-- The composition `Y_n ⟶ Y_{n+1} ⟶ X_{n+1}` identifies the two projections of the kernel
pair `R_n`, because `Y_{n+1} ⟶ X_{n+1}` identifies those of `R_{n+1}`. -/
theorem sourceStep_comp_π_equalizes (n : ℕ) :
    pullback.fst (N.glueMapAt n) (N.glueMapAt n) ≫ N.sourceStep n ≫ (D (n + 1)).π =
      pullback.snd (N.glueMapAt n) (N.glueMapAt n) ≫ N.sourceStep n ≫ (D (n + 1)).π := by
  rw [← Category.assoc, ← N.relationStep_comp_fst n, ← Category.assoc,
    ← N.relationStep_comp_snd n, Category.assoc, Category.assoc, (D (n + 1)).equalizes]

/-- **Stacks 0AGJ.** The morphism `X_n ⟶ X_{n+1}` of the tower
`X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X`, induced by the morphisms `Y_n ⟶ Y_{n+1}` and `R_n ⟶ R_{n+1}`. -/
@[stacks 0AGJ "the morphism of the tower"]
def towerMap (n : ℕ) : (D n).space ⟶ (D (n + 1)).space :=
  (D n).isColimit.desc
    (Cofork.ofπ (N.sourceStep n ≫ (D (n + 1)).π) (N.sourceStep_comp_π_equalizes D n))

@[simp]
theorem π_comp_towerMap (n : ℕ) :
    (D n).π ≫ N.towerMap D n = N.sourceStep n ≫ (D (n + 1)).π := by
  have h := Cofork.IsColimit.π_desc (s := Cofork.ofπ (D n).π (D n).equalizes)
    (t := Cofork.ofπ (N.sourceStep n ≫ (D (n + 1)).π) (N.sourceStep_comp_π_equalizes D n))
    (D n).isColimit
  rwa [Cofork.π_ofπ, Cofork.π_ofπ] at h

/-- **Stacks 0AGJ.** Each morphism of the tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X` is a morphism over
`X`: the triangle formed with the two morphisms to `X` commutes. -/
@[stacks 0AGJ "the tower is a tower over X"]
theorem towerMap_comp_toTarget (n : ℕ) :
    N.towerMap D n ≫ (D (n + 1)).toTarget = (D n).toTarget := by
  refine Cofork.IsColimit.hom_ext (D n).isColimit ?_
  rw [Cofork.π_ofπ, ← Category.assoc, N.π_comp_towerMap D n, Category.assoc,
    (D (n + 1)).fac, N.sourceStep_comp_glueMapAt, (D n).fac]

end ClosedSubspaceSystem

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
