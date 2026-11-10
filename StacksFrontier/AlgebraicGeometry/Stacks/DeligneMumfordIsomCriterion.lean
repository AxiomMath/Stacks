module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.PseudoTorsorProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomPresheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack

/-!
# Deligne–Mumford stacks through their automorphism group algebraic spaces

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site. This file proves that `𝒳` is
Deligne–Mumford over `S`, resp. quasi-Deligne–Mumford over `S`, exactly when for every scheme `T`
over `S` and every object `x` of `𝒳` over `T` the automorphism group algebraic space
`Isom_𝒳(x, x)` of **Stacks 04YP** is unramified, resp. locally quasi-finite, over `T`.

This is the form of **Stacks 0CL0**, parts (4) and (5), for the structure morphism `𝒳 ⟶ S`
which the proof of **Stacks 0DSN** uses. The source reads it off the cartesian squares in the
proof of **Stacks 0CL0**: the base change of the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_S 𝒳` along a
scheme-valued point `(x₁, x₂, α)` over `T` is `Isom_𝒳(x₁, x₂)`, a pseudo-torsor under
`Isom_𝒳(x₂, x₂)` by **Stacks 04YP**, part (2), and **Stacks 0DSK** passes unramifiedness and
local quasi-finiteness from the group to the pseudo-torsor.

## Main results

* `AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_algebraicSpaceMap_iff_isomSpace`: for a
  1-morphism whose target has faithful structure functor, a property tested on étale charts holds
  for the algebraic space representing a base change of the relative diagonal exactly when it
  holds for the isomorphism space of the two components of the point.
* `AlgebraicGeometry.Stack.isDMOver_iff_forall_isUnramified_isomSpaceOver` and
  `AlgebraicGeometry.Stack.isQuasiDMOver_iff_forall_isLocallyQuasiFinite_isomSpaceOver`: the
  pointwise criteria.

## Implementation notes

The target of the structure morphism is the slice of the site over `S`, whose structure functor
is the forgetful functor and hence faithful. Two vertical morphisms of it between the same
objects agree, so the presheaf of vertical morphisms of `𝒳` lying over the comparison
isomorphism of a point is the presheaf of all vertical morphisms between its components
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.isIso_relVertHomInclusion_of_faithful`).

## References

* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 0DSK](https://stacks.math.columbia.edu/tag/0DSK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₃} 𝒴]
  {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}
  {Y : 𝒯 ⥤ RelProd p q F}

/-- **Over a target with faithful structure functor the comparison condition is automatic.** If
`q` is faithful, every vertical morphism `Y₁ a ⟶ Y₂ a` lies over the comparison isomorphism of
`Y` at `a`, because both its image under `F` and that isomorphism are vertical morphisms between
the same two objects of `𝒴`. So the inclusion of the presheaf of vertical morphisms over the
comparison isomorphism into the presheaf of all vertical morphisms is an isomorphism. -/
theorem isIso_relVertHomInclusion_of_faithful [q.Faithful] (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    IsIso (relVertHomInclusion hq hp hY hF) := by
  refine (NatTrans.isIso_iff_isIso_app _).mpr fun a => ?_
  rw [isIso_iff_bijective]
  refine ⟨fun m n h => Subtype.ext h, fun m => ⟨⟨m, ?_⟩, rfl⟩⟩
  let m' : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a.unop := m
  apply q.map_injective
  have h₁ := (VertHom.pushforward hF m').2
  have h₂ : q.IsHomLift (𝟙 (p𝒯.obj a.unop)) (Y.obj a.unop).iso.hom := by
    have := (Y.obj a.unop).vertical
    rwa [base_eq_of_obj hY a.unop] at this
  exact (IsHomLift.fac' q (𝟙 (p𝒯.obj a.unop)) (VertHom.pushforward hF m').1).trans
    (IsHomLift.fac' q (𝟙 (p𝒯.obj a.unop)) (Y.obj a.unop).iso.hom).symm

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u w

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_deligneMumfordIsomCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_deligneMumfordIsomCriterion
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_deligneMumfordIsomCriterion.has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The every-étale-chart condition for a morphism into a terminal presheaf holds for one terminal
presheaf exactly when it holds for any other. -/
private theorem holdsOnEveryEtaleChart_iff_of_isTerminal {P : MorphismProperty Scheme.{u}}
    {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsTerminal G) (hG' : IsTerminal G')
    (f : F ⟶ G) (f' : F ⟶ G') :
    Space.HoldsOnEveryEtaleChart B S hS P f ↔ Space.HoldsOnEveryEtaleChart B S hS P f' :=
  ⟨Space.holdsOnEveryEtaleChart_of_isTerminal B S hS hG hG' f f',
    Space.holdsOnEveryEtaleChart_of_isTerminal B S hS hG' hG f' f⟩

/-- **The base change of a relative diagonal is the isomorphism space of the two components.**
Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks whose target has faithful structure functor,
and let `F` be an algebraic space representing the base change of the relative diagonal `Δ_f`
along a scheme-valued point `y = (x₁, x₂, α)` of `𝒳 ×_𝒴 𝒳` over `U`. Then any property tested on
étale charts holds for the structural morphism of `F` exactly when it holds for the structural
morphism of `Isom_𝒳(x₁, x₂)` over `U`. -/
theorem holdsOnEveryEtaleChart_algebraicSpaceMap_iff_isomSpace (P : MorphismProperty Scheme.{u})
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hq : 𝒴.val.val.p.Faithful)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U
          (Functor.sliceValue 𝒳.val.val.p U (Y₁' y) (h1' hy))
          (Functor.sliceValue 𝒳.val.val.p U (Y₂' y) (h2' hy)))) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨e⟩ := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w F).mp hE
  have hiso : relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
      f.hom.hom.w ≅ F :=
    ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u, u}).preimageIso e
  have _ := isIso_relVertHomInclusion_of_faithful 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w
  let iI : F ≅ isomSpace B S hS 𝒳.val U
      (Functor.sliceValue 𝒳.val.val.p U (Y₁' y) (h1' hy))
      (Functor.sliceValue 𝒳.val.val.p U (Y₂' y) (h2' hy)) :=
    hiso.symm ≪≫ asIso (relVertHomInclusion _ _ hy f.hom.hom.w) ≪≫
      Functor.vertHomPresheafIsoIsomPresheafOfFunctors 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids U (Y₁' y) (Y₂' y) (h1' hy) (h2' hy)
  let Ppre : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B S hS P g
  have _ : Ppre.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS P
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    Ppre.inverseImage (ObjectProperty.ι _)
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  refine (prop_algebraicSpaceMap_iff B S hS Q U F hF).trans ?_
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    P F).trans ?_
  refine (holdsOnEveryEtaleChart_iff_of_isTerminal B U.left.1 U.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ (terminal.from F)).trans ?_
  exact Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2 P iI

/-! ### Base change of the isomorphism space -/

/-- **A property of the isomorphism space at a pullback is a property of a base change.** Let
`m : x' ⟶ x` be a cartesian morphism of a category fibred in groupoids over `e : V ⟶ U`. Then a
property tested on étale charts holds for `Isom_𝒳(x', x') ⟶ V`, over `V`, exactly when it holds,
over `U`, for the base change of `Isom_𝒳(x, x) ⟶ U` along `V ⟶ U`; the latter is written as the
second projection of a pullback over any presheaf `T` with subsingleton values, which is how the
base `U` appears in the group algebraic spaces of Stacks 04YP. -/
theorem holdsOnEveryEtaleChart_isomSpace_iff_pullbackSnd (P : MorphismProperty Scheme.{u})
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U V : BigFppfOver B S hS} (e : V ⟶ U)
    {x : 𝒳.val.p.Fiber U} {x' : 𝒳.val.p.Fiber V} (m : x'.1 ⟶ x.1)
    (hm : 𝒳.val.p.IsStronglyCartesian e m)
    {T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u} (hT : ∀ W, Subsingleton (T.obj W))
    (π : isomSpace B S hS 𝒳 U x x ⟶ T) (τ : yoneda.obj (Over.mk e.left) ⟶ T) :
    Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 P
        (terminal.from (isomSpace B S hS 𝒳 V x' x')) ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P (pullback.snd π τ) := by
  let I := isomSpace B S hS 𝒳 U x x
  let R := (OverShriek.relocalizeRestrict e.left).obj I
  let iV : isomSpace B S hS 𝒳 V x' x' ≅ R := isomSpaceBaseChange B S hS 𝒳 e m hm
  let PU : MorphismProperty ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P g
  have _ : PU.RespectsIso :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B U.left.1 U.left.2 P
  have h₁ := (Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B V.left.1 V.left.2 P iV).trans
    (holdsOnEveryEtaleChart_iff_of_isTerminal B V.left.1 V.left.2 terminalIsTerminal
      (Over.mkIdTerminal.isTerminalObj yoneda _) _ (Space.toYonedaId B V.left.1 V.left.2 R))
  refine h₁.trans ((Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V.left.1 U.left.1
    V.left.2 U.left.2 e.left P R).symm.trans ?_)
  have hsq := OverShriek.isPullback_relocalizeRestrictCounit e.left I hT π τ
  have : HasPullback π τ := hasPullback_presheaf_deligneMumfordIsomCriterion π τ
  change PU (OverShriek.relocalizeToYoneda e.left R) ↔ PU (pullback.snd π τ)
  rw [← hsq.isoPullback_hom_snd]
  exact PU.cancel_left_of_respectsIso hsq.isoPullback.hom (pullback.snd π τ)

/-- **The isomorphism space is unchanged along a cartesian morphism over an isomorphism.** If
`m : x' ⟶ x` is a cartesian morphism of a category fibred in groupoids over an isomorphism
`e : V ⟶ U`, then a property tested on étale charts holds for `Isom_𝒳(x', x') ⟶ V` exactly when
it holds for `Isom_𝒳(x, x) ⟶ U`. -/
theorem holdsOnEveryEtaleChart_isomSpace_iff_of_isIso (P : MorphismProperty Scheme.{u})
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {U V : BigFppfOver B S hS} (e : V ⟶ U) [IsIso e]
    {x : 𝒳.val.p.Fiber U} {x' : 𝒳.val.p.Fiber V} (m : x'.1 ⟶ x.1)
    (hm : 𝒳.val.p.IsStronglyCartesian e m) :
    Space.HoldsOnEveryEtaleChart B V.left.1 V.left.2 P
        (terminal.from (isomSpace B S hS 𝒳 V x' x')) ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳 U x x)) := by
  let I := isomSpace B S hS 𝒳 U x x
  have _ : IsIso e.left := inferInstanceAs (IsIso ((Over.forget _).map e))
  let k : (Over.mk e.left : Over U.left) ⟶ Over.mk (𝟙 U.left) := Over.homMk e.left
  have _ : IsIso k :=
    ⟨⟨Over.homMk (CategoryTheory.inv e.left) (by simp), by ext; simp [k], by ext; simp [k]⟩⟩
  let τ : yoneda.obj (Over.mk e.left) ⟶ yoneda.obj (Over.mk (𝟙 U.left)) := yoneda.map k
  let π : I ⟶ yoneda.obj (Over.mk (𝟙 U.left)) := OverShriek.toYonedaMkId I
  refine (holdsOnEveryEtaleChart_isomSpace_iff_pullbackSnd B S hS P 𝒳 e m hm
    (fun W => OverShriek.subsingleton_yoneda_obj_mkId W) π τ).trans ?_
  let PU : MorphismProperty ((BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) :=
    fun _ _ g => Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P g
  have _ : PU.RespectsIso :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf B U.left.1 U.left.2 P
  have hsnd : pullback.snd π τ = pullback.fst π τ ≫ π ≫ CategoryTheory.inv τ := by
    rw [pullback.condition_assoc, IsIso.hom_inv_id, Category.comp_id]
  change PU (pullback.snd π τ) ↔ PU (terminal.from I)
  rw [hsnd, PU.cancel_left_of_respectsIso, PU.cancel_right_of_respectsIso]
  exact holdsOnEveryEtaleChart_iff_of_isTerminal B U.left.1 U.left.2
    (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _

/-! ### The criterion -/

section Criterion

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The isomorphism spaces of the objects of `𝒳` have a property its relative diagonal has.**
If every algebraic space representing a base change of the relative diagonal of `f`, whose
target has faithful structure functor, has a property tested on étale charts, then so has the
isomorphism space `Isom_𝒳(x, x) ⟶ U` of every object `x` of `𝒳` over a scheme `U`.

The base change along the point `(x, x, id)` of `𝒳 ×_𝒴 𝒳` is represented by the presheaf of
vertical morphisms over the comparison isomorphism, which is `Isom_𝒳(x̃, x̃)` for the chosen
pullback `x̃` of `x` along the identity of `U`, and `x̃ ⟶ x` is cartesian over an isomorphism. -/
theorem holdsOnEveryEtaleChart_isomSpace_of_relativeDiagonal (P : MorphismProperty Scheme.{u})
    (hq : 𝒴.val.val.p.Faithful)
    (h : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
        Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
          (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
      (terminal.from (isomSpace B S hS 𝒳.val U x x)) := by
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let p := 𝒳.val.val.p
  let W := Over.iteratedSliceBackward U ⋙ Functor.pullbackSliceFunctor p x
  have hW : W ⋙ p = Over.map U.hom := Functor.backward_pullbackSliceFunctor_comp p U x
  let Δ := relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom
  let y := W ⋙ Δ.toFunctor
  have hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom := by
    change W ⋙ (Δ.toFunctor ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom
      f.hom.hom).val.p) = _
    rw [Δ.w]
    exact hW
  have _ := isIso_relVertHomInclusion_of_faithful 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w
  let R := relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids hy
    f.hom.hom.w
  let iR : R ≅ isomSpace B S hS 𝒳.val U
      (Functor.sliceValue p U (Y₁' y) (h1' hy)) (Functor.sliceValue p U (Y₂' y) (h2' hy)) :=
    asIso (relVertHomInclusion _ _ hy f.hom.hom.w) ≪≫
      Functor.vertHomPresheafIsoIsomPresheafOfFunctors p
        𝒳.val.isFiberedInGroupoids U (Y₁' y) (Y₂' y) (h1' hy) (h2' hy)
  have hR : IsAlgebraicSpace B U.left.1 U.left.2 R :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2 iR
      (isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U _ _)
  have hE := (nonempty_equivalenceOver_fst_iff 𝒴.val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids hy f.hom.hom.w R).mpr ⟨Iso.refl _⟩
  have hslice := (holdsOnEveryEtaleChart_algebraicSpaceMap_iff_isomSpace B S hS P f hq U y hy
    R hR hE).mp (h U y hy R hR hE)
  -- The value of `W` at the terminal object is the chosen pullback of `x` along an isomorphism.
  let g := Functor.structHom U (Over.mk (𝟙 U.left))
  let e : U ⟶ U := eqToHom (Functor.overMap_obj_mkId U).symm ≫ g
  have he : e = 𝟙 U := by
    ext
    simp [e, g]
  have _ : IsIso e := by
    rw [he]
    infer_instance
  let m : (Functor.sliceValue p U (Y₁' y) (h1' hy)).1 ⟶ x.1 :=
    Functor.IsPreFibered.pullbackMap x.2 g
  have hlift : p.IsHomLift e m := by
    have : p.IsCartesian g m := Functor.IsPreFibered.pullbackMap.IsCartesian (p := p) x.2 g
    refine IsHomLift.of_fac' p e m (Functor.sliceValue p U (Y₁' y) (h1' hy)).2 x.2 ?_
    rw [IsHomLift.fac' p g m]
    simp [e]
  have hm : p.IsStronglyCartesian e m :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift e m
  exact (holdsOnEveryEtaleChart_isomSpace_iff_of_isIso B S hS P 𝒳.val e m hm).mp hslice

/-- **The relative diagonal has a property its isomorphism spaces have.** Conversely, let `P` be
a property tested on étale charts such that every isomorphism space `Isom_𝒳(x₁, x₂) ⟶ U` has `P`
as soon as `Isom_𝒳(x₂, x₂) ⟶ U` has it — which **Stacks 0DSK** supplies for unramifiedness and
local quasi-finiteness, `Isom_𝒳(x₁, x₂)` being a pseudo-torsor under `Isom_𝒳(x₂, x₂)` by
**Stacks 04YP**, part (2). If every automorphism space of `𝒳` has `P`, then so has every algebraic
space representing a base change of the relative diagonal of `f`, whose target has faithful
structure functor. -/
theorem relativeDiagonal_of_holdsOnEveryEtaleChart_isomSpace (P : MorphismProperty Scheme.{u})
    (hq : 𝒴.val.val.p.Faithful)
    (htorsor : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x₁ x₂ : 𝒳.val.val.p.Fiber U),
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
          (terminal.from (isomSpace B S hS 𝒳.val U x₂ x₂)) →
        Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
          (terminal.from (isomSpace B S hS 𝒳.val U x₁ x₂)))
    (hx : letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
      ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U x x)))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
    (hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
        (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Space.HoldsOnEveryEtaleChart B S hS P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  (holdsOnEveryEtaleChart_algebraicSpaceMap_iff_isomSpace B S hS P f hq U y hy F hF hE).mpr
    (htorsor U _ _ (hx U _))

end Criterion

/-! ### Deligne–Mumford and quasi-Deligne–Mumford stacks -/

section Absolute

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- A property tested on étale charts holds for the structural morphism of an isomorphism space
read over the site terminal space exactly when it holds for its morphism to the terminal
presheaf: both targets are terminal. -/
theorem holdsOnEveryEtaleChart_isomSpaceOver_hom_iff (P : MorphismProperty Scheme.{u})
    (U : BigFppfOver B S hS) (x₁ x₂ : 𝒳.val.val.p.Fiber U) :
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P (isomSpaceOver B S hS 𝒳.val U x₁ x₂).hom ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U x₁ x₂)) :=
  holdsOnEveryEtaleChart_iff_of_isTerminal B U.left.1 U.left.2
    (isTerminal_siteTerminalSpace B S hS U) terminalIsTerminal _ _

/-- **Stacks 0DSK at the isomorphism spaces of an algebraic stack, unramified case.**
`Isom_𝒳(x₁, x₂)` is unramified over `U` as soon as `Isom_𝒳(x₂, x₂)` is: it is a pseudo-torsor
under it by **Stacks 04YP**, part (2), and it is locally of finite type by **Stacks 04XR**. -/
theorem isUnramified_isomSpaceOver_of_isUnramified (U : BigFppfOver B S hS)
    (x₁ x₂ : 𝒳.val.val.p.Fiber U)
    (h : Space.IsUnramified B U.left.1 U.left.2 (isomSpaceOver B S hS 𝒳.val U x₂ x₂).hom) :
    Space.IsUnramified B U.left.1 U.left.2 (isomSpaceOver B S hS 𝒳.val U x₁ x₂).hom := by
  let : ModObj (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x₂).obj.X
      (isomSpaceOver B S hS 𝒳.val U x₁ x₂) := isomSpaceOverModObj B S hS 𝒳.val U x₁ x₂
  exact Space.isUnramified_of_isPseudoTorsor B U.left.1 U.left.2
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x₂) _
    (isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U x₁ x₂)
    ((holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₁ x₂).mpr
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U x₁ x₂))
    h (isomSpaceOver_isPseudoTorsor B S hS 𝒳.val U x₁ x₂)

/-- **Stacks 0DSK at the isomorphism spaces of an algebraic stack, locally quasi-finite case.**
`Isom_𝒳(x₁, x₂)` is locally quasi-finite over `U` as soon as `Isom_𝒳(x₂, x₂)` is. -/
theorem isLocallyQuasiFinite_isomSpaceOver_of_isLocallyQuasiFinite (U : BigFppfOver B S hS)
    (x₁ x₂ : 𝒳.val.val.p.Fiber U)
    (h : Space.IsLocallyQuasiFinite B U.left.1 U.left.2
      (isomSpaceOver B S hS 𝒳.val U x₂ x₂).hom) :
    Space.IsLocallyQuasiFinite B U.left.1 U.left.2 (isomSpaceOver B S hS 𝒳.val U x₁ x₂).hom := by
  let : ModObj (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x₂).obj.X
      (isomSpaceOver B S hS 𝒳.val U x₁ x₂) := isomSpaceOverModObj B S hS 𝒳.val U x₁ x₂
  exact Space.isLocallyQuasiFinite_of_isPseudoTorsor B U.left.1 U.left.2
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (automorphismGroupSpace B S hS 𝒳.val 𝒳.property U x₂) _
    (isAlgebraicSpace_isomSpace B S hS 𝒳.val 𝒳.property U x₁ x₂)
    ((holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₁ x₂).mpr
      (isLocallyOfFiniteType_isomPresheaf B S hS 𝒳.val 𝒳.property U x₁ x₂))
    h (isomSpaceOver_isPseudoTorsor B S hS 𝒳.val U x₁ x₂)

/-- The structure functor of the algebraic stack represented by the base is faithful: it is the
forgetful functor of a slice. -/
theorem faithful_schemeStack_p :
    (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val.val.p.Faithful :=
  inferInstanceAs (Over.forget _).Faithful

/-- **An algebraic stack is Deligne–Mumford over `S` exactly when its automorphism group algebraic
spaces are unramified.** For every scheme `U` over `S` and every object `x` of `𝒳` over `U`, the
group algebraic space `Isom_𝒳(x, x)` of **Stacks 04YP** is unramified over `U`. -/
theorem isDMOver_iff_forall_isUnramified_isomSpaceOver :
    IsDMOver B S hS 𝒳 ↔ ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.IsUnramified B U.left.1 U.left.2 (isomSpaceOver B S hS 𝒳.val U x x).hom := by
  constructor
  · intro h U x
    exact (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).mpr
      (holdsOnEveryEtaleChart_isomSpace_of_relativeDiagonal B S hS (structureMorphism B S hS 𝒳)
        _ (faithful_schemeStack_p.{u, w} B S hS) h.2 U x)
  · intro h
    refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      (structureMorphism B S hS 𝒳), fun U y hy F hF hE => ?_⟩
    exact relativeDiagonal_of_holdsOnEveryEtaleChart_isomSpace B S hS
      (structureMorphism B S hS 𝒳) _ (faithful_schemeStack_p.{u, w} B S hS)
      (fun U x₁ x₂ hx => (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₁ x₂).mp
        (isUnramified_isomSpaceOver_of_isUnramified B S hS 𝒳 U x₁ x₂
          ((holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₂ x₂).mpr hx)))
      (fun U x => (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).mp (h U x))
      U y hy F hF hE

/-- **An algebraic stack is quasi-Deligne–Mumford over `S` exactly when its automorphism group
algebraic spaces are locally quasi-finite.** -/
theorem isQuasiDMOver_iff_forall_isLocallyQuasiFinite_isomSpaceOver :
    IsQuasiDMOver B S hS 𝒳 ↔ ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U),
      Space.IsLocallyQuasiFinite B U.left.1 U.left.2 (isomSpaceOver B S hS 𝒳.val U x x).hom := by
  constructor
  · intro h U x
    exact (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).mpr
      (holdsOnEveryEtaleChart_isomSpace_of_relativeDiagonal B S hS (structureMorphism B S hS 𝒳)
        _ (faithful_schemeStack_p.{u, w} B S hS) h U x)
  · intro h U y hy F hF hE
    exact relativeDiagonal_of_holdsOnEveryEtaleChart_isomSpace B S hS
      (structureMorphism B S hS 𝒳) _ (faithful_schemeStack_p.{u, w} B S hS)
      (fun U x₁ x₂ hx => (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₁ x₂).mp
        (isLocallyQuasiFinite_isomSpaceOver_of_isLocallyQuasiFinite B S hS 𝒳 U x₁ x₂
          ((holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x₂ x₂).mpr hx)))
      (fun U x => (holdsOnEveryEtaleChart_isomSpaceOver_hom_iff B S hS 𝒳 _ U x x).mp (h U x))
      U y hy F hF hE

end Absolute

/-! ### Isomorphism spaces in a full subcategory -/

/-- **The isomorphism spaces of an algebraic full subcategory are those of the ambient stack.** For
an object `x` of a full subcategory of an algebraic stack `𝒳` which is itself an algebraic stack,
a property tested on étale charts holds for `Isom(x, x) ⟶ U` computed in the subcategory exactly
when it holds for `Isom_𝒳(x, x) ⟶ U`: the inclusion is fully faithful and preserves strongly
cartesian morphisms, so it identifies the two isomorphism sheaves (Stacks 042V). -/
theorem holdsOnEveryEtaleChart_isomSpace_fullSubcategory_iff (P : MorphismProperty Scheme.{u})
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (Q : ObjectProperty 𝒳.val.val.obj)
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q))
    (U : BigFppfOver B S hS) (x : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.Fiber U) :
    letI : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.IsFibered :=
      (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids.isFibered
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val U x x)) ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (terminal.from (isomSpace B S hS 𝒳.val U ⟨x.1.obj, x.2⟩ ⟨x.1.obj, x.2⟩)) := by
  let : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.IsFibered :=
    (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids.isFibered
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let ι := (fullSubcategoryInclusion 𝒳 Q hQ).hom.hom
  have hF : Functor.IsFibredOneMorphism (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p
      𝒳.val.val.p ι.toFunctor :=
    { comp_eq := ι.w
      map_isStronglyCartesian := fun f _ _ φ _ => by
        have : 𝒳.val.val.p.IsHomLift f (ι.toFunctor.map φ) :=
          Functor.isHomLift_map_of_comp_eq (p := (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p)
            ι.w f φ
        exact 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift f (ι.toFunctor.map φ) }
  let e : (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.val.p.isomPresheaf x x ⋙
      uliftFunctor.{u, u} ≅ 𝒳.val.val.p.isomPresheaf
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj x) :=
    liftedIsomPresheafIso hF (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val.isFiberedInGroupoids
      𝒳.val.isFiberedInGroupoids x x
  let e' : isomSpace B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hQ).val U x x ≅
      isomSpace B S hS 𝒳.val U ⟨x.1.obj, x.2⟩ ⟨x.1.obj, x.2⟩ :=
    Functor.isoWhiskerLeft _ ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ uliftFunctorTrivial.{u}.symm ≪≫ e)
  exact Space.holdsOnEveryEtaleChart_terminal_iff_of_iso B U.left.1 U.left.2 P e'

end AlgebraicGeometry.Stack

end
