module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite shriek presentations of constructible sheaves of `ℤ`-modules

The library's unconditional Stacks 095N,
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`, is stated for a
Noetherian ring `Λ : Type (u + 1)`: its proof reaches the presentation through
`AlgebraicGeometry.moduleShriekConstantIsoFree` and so through `ModuleCat.free Λ`, whose source
`Type u ⥤ ModuleCat.{u} Λ` ties the module universe to the ring universe. The ring `ℤ` lives in
`Type 0`, so 095N cannot be read at `ℤ` with sheaves of modules in `ModuleCat.{u + 1} ℤ`, which
is the shape every consumer of the abelian theory needs.

This file closes that gap by a universe transport. The ring `ULift.{u + 1} ℤ` *does* live in
`Type (u + 1)`, it is Noetherian, and restriction of scalars along `ULift.ringEquiv` is an
equivalence `ModuleCat.{u + 1} ℤ ≌ ModuleCat.{u + 1} (ULift.{u + 1} ℤ)` — the two universes of
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv` being independent. So 095N may be read at
`ULift.{u + 1} ℤ` and transported back to `ℤ`, which needs exactly two things: that
constructibility is carried across the equivalence of sheaf categories it induces, and that the
generators `j_{U!}\underline{ℤ}_U` of a presentation correspond to each other under it.

## Main results

* `AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int` — a
  constructible sheaf of `ℤ`-modules on `X_étale` is the cokernel of a map between finite direct
  sums of extensions by zero of constant free rank-one `ℤ`-module sheaves at quasi-compact
  quasi-separated étale objects. This is the forward half of Stacks 095N at `Λ = ℤ`.
* `AlgebraicGeometry.moduleShriekConstantUliftIntIso` — the generators correspond: restriction of
  scalars carries `j_{U!}\underline{ℤ}_U` to `j_{U!}\underline{ULift ℤ}_U`.
* `AlgebraicGeometry.hasFiniteShriekPresentation_int_of_uliftInt` — a finite shriek presentation
  of the associated sheaf of `ULift ℤ`-modules is one of the original sheaf of `ℤ`-modules.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence` — finite local
  constancy is carried along a change of coefficients into a category of modules.
* `AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntEquivalence` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntRestrictScalars` — the two transports of
  constructibility this uses, from abelian sheaves and from sheaves of `ℤ`-modules.

## Implementation notes

Stacks 095N is an identification of two categories, so the tag covers both directions. Only the
forward one is transported here, because that is the direction the consumers need; the tag
therefore stays on `AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`,
which proves it in full for every Noetherian ring in `Type (u + 1)`, and is not repeated on the
specialisation below.

The transport of a presentation is mechanical once the generators are matched: the induced
equivalence of sheaf categories is additive, hence preserves the finite coproducts and the
cokernel out of which a presentation is built.

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u s t a r va

/-- `ULift ℤ` is a Noetherian ring, being isomorphic to `ℤ`. -/
public instance isNoetherianRing_uliftInt : IsNoetherianRing (ULift.{t} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv (R := ℤ)).symm

namespace ModuleCat

/-- A module-finite module over `S` is module-finite over `R` when restricted along a ring
isomorphism `R ≃+* S`: the identity is a surjective semilinear map for the inverse isomorphism. -/
public theorem moduleFinite_restrictScalars_of_ringEquiv
    {R : Type*} [Ring R] {S : Type*} [Ring S] (φ : R ≃+* S)
    (M : ModuleCat.{w} S) [Module.Finite S M] :
    Module.Finite R ((ModuleCat.restrictScalars φ.toRingHom).obj M) :=
  Module.Finite.of_surjective (σ := φ.symm.toRingHom)
    (R := S) (M := M) (S := R) (P := ((ModuleCat.restrictScalars φ.toRingHom).obj M : Type w))
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        show r • m = (φ.toRingHom (φ.symm r)) • m
        rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] }
    Function.surjective_id

/-- `ℤ`-modules are the same thing as `ULift ℤ`-modules, by restriction of scalars along
`ULift.ringEquiv`. The module universe is unconstrained by the universe of the lift, which is the
whole point: it lets a statement about `ModuleCat.{s} ℤ` be read at a ring in `Type t`. -/
public abbrev restrictScalarsUliftIntEquivalence :
    ModuleCat.{s} ℤ ≌ ModuleCat.{s} (ULift.{t} ℤ) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv (R := ℤ))

/-- The free rank-one `ULift ℤ`-module is the universe lift of `ℤ` with its scalars restricted
along `ULift.ringEquiv`: both are the additive group `ULift ℤ`, and a scalar of `ULift ℤ` acts in
both cases by multiplication of the integers underneath. -/
public def restrictScalarsUliftIntSelfIso :
    restrictScalarsUliftIntEquivalence.{s, s}.functor.obj (ModuleCat.of ℤ (ULift.{s} ℤ)) ≅
      ModuleCat.of (ULift.{s} ℤ) (ULift.{s} (ULift.{s} ℤ)) :=
  LinearEquiv.toModuleIso
    { toFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := by intro z x; ext; change z.down * x.down = _; rfl
      invFun := ULift.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end ModuleCat

namespace AddCommGrpCat

/-- Abelian groups are the same thing as `ULift ℤ`-modules: compose the equivalence with
`ℤ`-modules with restriction of scalars along `ULift.ringEquiv`. Unlike
`AddCommGrpCat.moduleCatIntEquivalence` this puts the ring in a universe of its own choosing,
which is what makes a statement about Noetherian rings in `Type (u + 1)` available for abelian
sheaves with coefficients in `Type (u + 1)`. -/
@[sga "3 I 3.1.3" "special case", sga "4 IV 11.1.5" "punctual topos"]
public abbrev moduleCatUliftIntEquivalence : AddCommGrpCat.{s} ≌ ModuleCat.{s} (ULift.{t} ℤ) :=
  AddCommGrpCat.moduleCatIntEquivalence.{s}.trans
    ModuleCat.restrictScalarsUliftIntEquivalence.{s, t}

end AddCommGrpCat

namespace Stacks.ConstantSheaf

/-- Finite local constancy is carried along a change of coefficients `e : A ≌ ModuleCat R`, for
any class `P` of objects of `A` whose image under `e` consists of finitely generated modules: the
same trivialising cover works, and the constant sheaf commutes with the change of coefficients by
`CategoryTheory.Sheaf.constantSheafCoefficientIso`.

The hypothesis is the content of `Stacks.ConstantSheaf.IsFiniteLocallyConstant` and of
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` with the condition on the constant values left
as the parameter `P`, so that both notions can be fed to it. -/
public theorem isFiniteTypeLocallyConstant_of_coefficientEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type a} [Category.{va} A] {R : Type r} [Ring R] (e : A ≌ ModuleCat.{w} R)
    [∀ V : C, HasWeakSheafify (J.over V) A]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    [∀ V : C, (J.over V).HasSheafCompose e.functor]
    [∀ V : C, (J.over V).HasSheafCompose e.inverse]
    [J.HasSheafCompose e.functor]
    (P : A → Prop) (hP : ∀ M : A, P M → ModuleCat.isFG R (e.functor.obj M))
    (F : Sheaf J A)
    (hF : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, ∃ M : A, P M ∧
        Nonempty ((constantSheaf (J.over (V i)) A).obj M ≅ (J.overPullback A (V i)).obj F))
    (Q : Sheaf J (ModuleCat.{w} R))
    (eQ : (sheafCompose J e.functor).obj F ≅ Q) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J Q := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hF U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hV i
  refine ⟨e.functor.obj M, hP M hM, ⟨?_⟩⟩
  exact ((Sheaf.constantSheafCoefficientIso (J.over (V i)) e).app M).symm ≪≫
    (sheafCompose (J.over (V i)) e.functor).mapIso eM ≪≫
    (J.overPullback (ModuleCat.{w} R) (V i)).mapIso eQ

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- A finite locally constant sheaf of abelian groups becomes, under the equivalence with
`ULift ℤ`-modules, a locally constant sheaf of finitely generated `ULift ℤ`-modules. This is
`AlgebraicGeometry.isFiniteTypeLocallyConstant_moduleCatIntEquivalence` with the ring lifted into
the coefficient universe; a finite abelian group is a finitely generated module over any ring. -/
public theorem isFiniteTypeLocallyConstant_uliftIntEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v a}]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max u v a} (ULift.{max u v a} ℤ))]
    (F : Sheaf J AddCommGrpCat.{max u v a})
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant J F)
    (Q : Sheaf J (ModuleCat.{max u v a} (ULift.{max u v a} ℤ)))
    (eQ : (sheafCompose J
      AddCommGrpCat.moduleCatUliftIntEquivalence.{max u v a, max u v a}.functor).obj F ≅ Q) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ULift.{max u v a} ℤ) J Q := by
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence J
    AddCommGrpCat.moduleCatUliftIntEquivalence.{max u v a, max u v a}
    (fun M => Finite M) (fun M hM => ?_) F hF.exists_finite_cover Q eQ
  have : Finite ((𝟭 AddCommGrpCat.{max u v a}).obj M) := hM
  have : Finite (AddCommGrpCat.moduleCatUliftIntEquivalence.{max u v a,
      max u v a}.functor.obj M) :=
    Finite.of_injective (AddCommGrpCat.moduleCatIntEquivalence.unitIso.inv.app M).hom
      (ConcreteCategory.bijective_of_isIso
        (AddCommGrpCat.moduleCatIntEquivalence.unitIso.inv.app M)).1
  exact (ModuleCat.isFG_iff _).2 Module.Finite.of_finite

/-- A locally constant sheaf of finitely generated `ℤ`-modules becomes, under restriction of
scalars along `ULift.ringEquiv`, a locally constant sheaf of finitely generated
`ULift ℤ`-modules: the same trivialising cover works, and finite generation is preserved by
restriction of scalars along a ring isomorphism. -/
public theorem isFiniteTypeLocallyConstant_uliftIntRestrictScalars
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max u v a} ℤ)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{max u v a} (ULift.{max u v a} ℤ))]
    (F : Sheaf J (ModuleCat.{max u v a} ℤ))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant ℤ J F)
    (Q : Sheaf J (ModuleCat.{max u v a} (ULift.{max u v a} ℤ)))
    (eQ : (sheafCompose J
      ModuleCat.restrictScalarsUliftIntEquivalence.{max u v a,
        max u v a}.functor).obj F ≅ Q) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ULift.{max u v a} ℤ) J Q := by
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence J
    ModuleCat.restrictScalarsUliftIntEquivalence.{max u v a, max u v a}
    (fun M => ModuleCat.isFG ℤ M) (fun M hM => ?_) F hF Q eQ
  have := (ModuleCat.isFG_iff _).1 hM
  exact (ModuleCat.isFG_iff _).2
    (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (ULift.ringEquiv (R := ℤ)) M)

/-- A constructible sheaf of abelian groups on the small étale site becomes a constructible sheaf
of `ULift ℤ`-modules. This is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence` with the ring lifted into
the coefficient universe, which is what makes the module theory over a Noetherian ring in
`Type (u + 1)` applicable to it. -/
public theorem isConstructibleModuleSheaf_uliftIntEquivalence
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) AddCommGrpCat.{u + 1}]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}).functor.obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  exact isFiniteTypeLocallyConstant_uliftIntEquivalence.{u, u + 1, 0} _ _ (hs i) _
    ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
      AddCommGrpCat.moduleCatUliftIntEquivalence.{u + 1, u + 1}).app F)

/-- A constructible sheaf of `ℤ`-modules on the small étale site becomes a constructible sheaf of
`ULift ℤ`-modules under restriction of scalars along `ULift.ringEquiv`. The same constructible
stratification works; only the coefficient translation has to be pushed past restriction to a
stratum. -/
public theorem isConstructibleModuleSheaf_uliftIntRestrictScalars
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ))
    (hF : IsConstructibleModuleSheaf B X ℤ F) :
    IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).functor.obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  exact isFiniteTypeLocallyConstant_uliftIntRestrictScalars.{u, u + 1, 0} _ _ (hs i) _
    ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app F)

/-- **The generators of a shriek presentation correspond under restriction of scalars.** The
extension by zero of the constant free rank-one `ℤ`-module sheaf at an étale object `U` of `X`
becomes the extension by zero of the constant free rank-one `ULift ℤ`-module sheaf at `U`.

Both sides are the inverse image along `U → X` of a constant sheaf, so the comparison is the
compatibility of the inverse image and of the constant sheaf with a change of coefficients —
`CategoryTheory.Sheaf.sheafPullbackCoefficientIso` and
`CategoryTheory.Sheaf.constantSheafCoefficientIso` — together with the identification
`ModuleCat.restrictScalarsUliftIntSelfIso` of the two constant values. -/
public def moduleShriekConstantUliftIntIso (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.1 X.property) :
    (sheafCompose (SmallEtale.topology B X.1 X.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.functor).obj
        (moduleShriekConstant.{u, 0, u + 1} B X ℤ U) ≅
      moduleShriekConstant.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ) U := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B U.obj.left ℤ
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ)
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left (ULift.{u + 1} ℤ)
  let := (SmallEtale.finalIsTerminal B U.obj.left.1 U.obj.left.property).hasTerminal
  refine (sheafCompose (SmallEtale.topology B X.1 X.property)
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.functor).mapIso
    (((Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtalePostcompose B X.1 X.property U) (ModuleCat.{u + 1} ℤ)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)).app _).symm) ≪≫ ?_
  refine (Sheaf.sheafPullbackCoefficientIso (smallEtalePostcompose B X.1 X.property U)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property)
    ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app _ ≪≫ ?_
  refine ((smallEtalePostcompose B X.1 X.property U).sheafPullback
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.1 X.property)).mapIso
    ((Sheaf.constantSheafCoefficientIso
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app _ ≪≫
      (constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapIso
          ModuleCat.restrictScalarsUliftIntSelfIso.{u + 1}) ≪≫ ?_
  exact (Functor.sheafPullbackConstruction.sheafPullbackIso
    (smallEtalePostcompose B X.1 X.property U) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X.1 X.property)).app _

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **A finite shriek presentation descends along restriction of scalars.** If the sheaf of
`ULift ℤ`-modules attached to a sheaf `G` of `ℤ`-modules is the cokernel of a map between finite
direct sums of extensions by zero of constant free rank-one `ULift ℤ`-module sheaves at étale
objects satisfying `P`, then `G` is the cokernel of a map between the corresponding direct sums of
`ℤ`-module sheaves.

The equivalence of sheaf categories induced by restriction of scalars is additive, so it preserves
the finite coproducts and the cokernel out of which the presentation is built; the generators are
matched by `AlgebraicGeometry.moduleShriekConstantUliftIntIso`. -/
public theorem hasFiniteShriekPresentation_int_of_uliftInt (B : BigEtaleSite.{u}) (X : B.Scheme)
    (P : SmallEtale B X.1 X.property → Prop)
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} ℤ))
    (h : HasFiniteShriekPresentation.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ) P
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).functor.obj G)) :
    HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ P G := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X ℤ
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ)
  set E := Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
    ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}
  have : E.functor.Additive := by constructor; intro F₁ F₂ p q; ext V : 3; rfl
  obtain ⟨n, m, Us, Vs, hU, hV, f, ⟨ef⟩⟩ := h
  have η : ∀ W : SmallEtale B X.1 X.property,
      E.inverse.obj (moduleShriekConstant.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ) W) ≅
        moduleShriekConstant.{u, 0, u + 1} B X ℤ W := fun W =>
    (E.unitIso.app _ ≪≫ E.inverse.mapIso (moduleShriekConstantUliftIntIso B X W)).symm
  have σ : ∀ {k : ℕ} (W : Fin k → SmallEtale B X.1 X.property),
      E.inverse.obj
          (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X (ULift.{u + 1} ℤ) (W i)) ≅
        ∐ fun i => moduleShriekConstant.{u, 0, u + 1} B X ℤ (W i) := fun W =>
    PreservesCoproduct.iso E.inverse _ ≪≫ Sigma.mapIso fun i => η (W i)
  have eG : cokernel f ≅ E.functor.obj G :=
    (sheafToPresheaf (SmallEtale.topology B X.1 X.property)
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).preimageIso
      (ef ≪≫ Functor.isoWhiskerLeft _
          (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} (ULift.{u + 1} ℤ)) ≪≫
        Functor.rightUnitor _)
  refine ⟨n, m, Us, Vs, hU, hV, (σ Vs).inv ≫ E.inverse.map f ≫ (σ Us).hom, ⟨?_⟩⟩
  have ecok : cokernel ((σ Vs).inv ≫ E.inverse.map f ≫ (σ Us).hom) ≅ G :=
    cokernel.mapIso _ (E.inverse.map f) (σ Vs).symm (σ Us).symm (by simp) ≪≫
      (PreservesCokernel.iso E.inverse f).symm ≪≫ E.inverse.mapIso eG ≪≫
        (E.unitIso.app G).symm
  refine (sheafToPresheaf (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{u + 1} ℤ)).mapIso ecok ≪≫ ?_
  exact (Functor.isoWhiskerLeft G.obj (ModuleCat.uliftFunctorSelfIso.{0, u + 1} ℤ) ≪≫
    G.obj.rightUnitor).symm

/-- **The forward half of Stacks 095N at the ring of integers.** Let `X` be a quasi-compact and
quasi-separated scheme. Every constructible sheaf of `ℤ`-modules on `X_étale` is the cokernel of a
map between finite direct sums of extensions by zero of constant free rank-one `ℤ`-module sheaves
at quasi-compact quasi-separated objects of `X_étale`.

No input is assumed. The library's Stacks 095N,
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`, is not available at
`ℤ`, whose universe is `0` while the coefficient universe is `u + 1`; it is applied instead at
`ULift.{u + 1} ℤ`, which is a Noetherian ring in `Type (u + 1)`, and the result is transported
back along restriction of scalars by
`AlgebraicGeometry.hasFiniteShriekPresentation_int_of_uliftInt`.

The shape is that of the hypothesis `h095N` of
`AlgebraicGeometry.isConstructibleAbelianSheaf_pullback_iff_of_surjective` and of
`AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleAbelianSheaf`, which is what it is
for. -/
public theorem hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} ℤ)] :
    ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} ℤ),
      IsConstructibleModuleSheaf B X ℤ G →
        HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ (IsQCQSEtaleObject B X) G :=
  fun G hG =>
    hasFiniteShriekPresentation_int_of_uliftInt B X _ G
      ((isConstructibleModuleSheaf_iff_qcqsShriekPresentation B X (ULift.{u + 1} ℤ) _).1
        (isConstructibleModuleSheaf_uliftIntRestrictScalars B X G hG))

end AlgebraicGeometry

end
