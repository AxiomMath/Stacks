module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct

/-!
# Fibre products in the big crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)`.  Given two morphisms
`(U₁, T₁, δ₁) ⟶ (U, T, δ)` and `(U₂, T₂, δ₂) ⟶ (U, T, δ)` of `CRIS(X/S)`, the fibre product is
built from the two fibre products already available: the fibre product `T₁ ×_T T₂` of the ambient
divided power schemes, [Stacks, Tag 07ME], and the fibre product `U₁ ×_U U₂` of the thickened
schemes.  The thickened scheme of the fibre product is the closed fibre of the ambient one,
because the closed fibre of a fibre product of divided power schemes is the fibre product of the
closed fibres, so no new divided power structure has to be constructed: the ambient divided power
scheme of the fibre product *is* `T₁ ×_T T₂`.

The one thing that must be checked is that the resulting immersion `U₁ ×_U U₂ ↪ T₁ ×_T T₂` is
again a thickening.  It is a closed immersion because it is a closed fibre inclusion up to
isomorphism, and it is surjective because its composite with the closed immersion
`T₁ ×_T T₂ ↪ T₁ ×_T T₂` of underlying schemes (`Crystalline.DividedPowerScheme.
underlyingPullbackComparison`) is the map of ordinary fibre products induced by the three
immersions, and a map of fibre products whose two outer components are surjective and whose base
component is a monomorphism is surjective.

## Main definitions

* `Crystalline.SchemeThickening.closedFiberSourceIso` — the thickened scheme of a divided power
  thickening of schemes is the closed fibre of its ambient divided power scheme.
* `Crystalline.GlobalCrystallineSituation.pullbackObject`,
  `Crystalline.GlobalCrystallineSituation.pullbackFst` and
  `Crystalline.GlobalCrystallineSituation.pullbackSnd` — the fibre product of two morphisms of
  `CRIS(X/S)` and its two projections.

## Main results

* **`Crystalline.GlobalCrystallineSituation.instHasPullbacksThickening`** — `CRIS(X/S)` has fibre
  products.  This is part of the first assertion of [Stacks, Tag 07I9].
* `Crystalline.SchemeThickening.closedFiberι_ker_eq` — the closed fibre inclusion of the ambient
  divided power scheme of a divided power thickening cuts out the same ideal sheaf as the
  immersion.
* `Crystalline.GlobalCrystallineSituation.pullbackImmersion_isThickening` — the immersion of the
  fibre product is a thickening.

## What is and is not proved

[Stacks, Tag 07I9] has two assertions.  The second, that the forgetful functor of
[Stacks, Tag 07I7] commutes with limits, is
`Crystalline.GlobalCrystallineSituation.forget_preservesLimits`.  The first asserts that
`CRIS(X/S)` has *all* finite nonempty limits, "in particular products of pairs and fibre
products".  **Only the fibre products are proved here.**

Binary products are not, and they are not a corollary of what is here: the product of
`(U₁, T₁, δ₁)` and `(U₂, T₂, δ₂)` is *not* the object with ambient scheme `T₁ ×_S T₂`.  The closed
fibre of `T₁ ×_S T₂` is `U₁ ×_{S₀} U₂`, whereas the thickened scheme of the product has to be
`U₁ ×_X U₂`, which is a closed subscheme of `U₁ ×_{S₀} U₂` and in general a proper one — the
immersion `U₁ ×_X U₂ ↪ T₁ ×_S T₂` is therefore not surjective, so the pair is not a divided power
thickening.  The affine model of the correct construction, [Stacks, Tag 07HN], cuts `T₁ ×_S T₂`
down by the ideal of `U₁ ×_X U₂` and then takes the *divided power envelope* of that ideal.

Binary products are proved too, elsewhere: the divided power envelope of an ideal in a ring is
`Crystalline.dividedPowerEnvelope`, the affine statement [Stacks, Tag 07HN] is formalized as
`Crystalline.DividedPowerThickening.instHasNonemptyFiniteColimits`, and the passage from that
affine statement to a global one — which the source performs by gluing over affine charts of `T₁`
and `T₂` — is carried out across the `BigSite/BinaryProduct*` modules, ending in
`Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening` of
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductInstance.lean`.

So all of clause (1) of [Stacks, Tag 07I9] holds, and the general statement is
`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening` in that module.  The
instance below remains worth having on its own: it constructs the fibre product directly, from the
divided power envelope of [Stacks, Tag 07ME], rather than deducing it from binary products and
equalizers through `nonempty_finite_limits_tfae`.

## References

* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open Stacks.Thickenings

universe u

namespace Crystalline

/-- **Over an affine open the divided power ideal is the kernel ideal of the closed fibre
inclusion.**  Over an affine open a section dies on the closed fibre exactly when it lies in the
divided power ideal, `Crystalline.DividedPowerScheme.ClosedFiberPresentation.app_eq_zero_iff`. -/
private theorem ker_ideal_closedFiberι (X : DividedPowerScheme.{u})
    (V : X.scheme.affineOpens) :
    (DividedPowerScheme.closedFiberι X).ker.ideal V =
      X.ideal.obj (op (V : X.scheme.Opens)) := by
  rw [Scheme.Hom.ker_apply]
  refine SetLike.ext fun s ↦ ?_
  rw [RingHom.mem_ker]
  exact (DividedPowerScheme.closedFiberPresentation X).app_eq_zero_iff V s

namespace SchemeThickening

variable (D : SchemeThickening.{u})

/-- **The immersion of a divided power thickening of schemes and the closed fibre inclusion of its
ambient divided power scheme cut out the same ideal sheaf.**  Both are the divided power ideal:
for the immersion this is the field `Crystalline.SchemeThickening.ideal_eq_ker`, for the closed
fibre inclusion it is the defining property of the closed fibre. -/
theorem closedFiberι_ker_eq :
    (DividedPowerScheme.closedFiberι D.target).ker = D.immersion.ker := by
  ext1
  funext V
  rw [ker_ideal_closedFiberι D.target V]
  exact D.ideal_eq_ker V

/-- **The thickened scheme of a divided power thickening of schemes is the closed fibre of its
ambient divided power scheme.**  Two closed immersions into the same scheme cutting out the same
ideal sheaf differ by a unique isomorphism, and the two ideal sheaves agree by
`Crystalline.SchemeThickening.closedFiberι_ker_eq`. -/
def closedFiberSourceIso : DividedPowerScheme.closedFiber D.target ≅ D.source :=
  haveI : IsIso (IsClosedImmersion.lift D.immersion
      (DividedPowerScheme.closedFiberι D.target) D.closedFiberι_ker_eq.ge) :=
    IsClosedImmersion.isIso_lift _ _ D.closedFiberι_ker_eq.symm
  asIso (IsClosedImmersion.lift D.immersion (DividedPowerScheme.closedFiberι D.target)
    D.closedFiberι_ker_eq.ge)

/-- The identification of the thickened scheme with the closed fibre is compatible with the two
closed immersions into the ambient scheme. -/
@[reassoc]
theorem closedFiberSourceIso_hom_immersion :
    D.closedFiberSourceIso.hom ≫ D.immersion = DividedPowerScheme.closedFiberι D.target :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse form of `Crystalline.SchemeThickening.closedFiberSourceIso_hom_immersion`. -/
@[reassoc]
theorem closedFiberSourceIso_inv_closedFiberι :
    D.closedFiberSourceIso.inv ≫ DividedPowerScheme.closedFiberι D.target = D.immersion := by
  rw [← D.closedFiberSourceIso_hom_immersion, Iso.inv_hom_id_assoc]

end SchemeThickening

/-- The first projection of the comparison map that enlarges the base of a fibre product. -/
private theorem pullback_mapDesc_fst {𝒜 : Type*} [Category 𝒜] {X Y Z T : 𝒜} (f : X ⟶ Z)
    (g : Y ⟶ Z) (i : Z ⟶ T) [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] :
    pullback.mapDesc f g i ≫ pullback.fst (f ≫ i) (g ≫ i) = pullback.fst f g :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second projection of the comparison map that enlarges the base of a fibre product. -/
private theorem pullback_mapDesc_snd {𝒜 : Type*} [Category 𝒜] {X Y Z T : 𝒜} (f : X ⟶ Z)
    (g : Y ⟶ Z) (i : Z ⟶ T) [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] :
    pullback.mapDesc f g i ≫ pullback.snd (f ≫ i) (g ≫ i) = pullback.snd f g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **Composing both legs of a fibre product with a monomorphism does not change the fibre
product.**  The inverse is the lift of the two projections, whose compatibility is the original
one after cancelling the monomorphism. -/
private theorem pullback_mapDesc_isIso {𝒜 : Type*} [Category 𝒜] [HasPullbacks 𝒜]
    {X Y Z T : 𝒜} (f : X ⟶ Z) (g : Y ⟶ Z) (i : Z ⟶ T) [Mono i] :
    IsIso (pullback.mapDesc f g i) := by
  have hcond : pullback.fst (f ≫ i) (g ≫ i) ≫ f = pullback.snd (f ≫ i) (g ≫ i) ≫ g :=
    (cancel_mono i).mp (by simp only [Category.assoc, pullback.condition])
  refine ⟨⟨pullback.lift (pullback.fst (f ≫ i) (g ≫ i)) (pullback.snd (f ≫ i) (g ≫ i)) hcond,
    ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback_mapDesc_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback_mapDesc_snd, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback_mapDesc_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback_mapDesc_snd, pullback.lift_snd, Category.id_comp]

/-- **A map of fibre product squares is surjective as soon as its two outer components are
surjective and its base component is a monomorphism.**  It factors as the isomorphism
`Crystalline.pullback_mapDesc_isIso` followed by a map of fibre products over a fixed base, and
surjectivity of schemes is stable under base change and composition. -/
private theorem pullback_map_surjective {X Y Z X' Y' Z' : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
    (i : X ⟶ X') (j : Y ⟶ Y') (k : Z ⟶ Z') [Mono k]
    (hi : Function.Surjective i) (hj : Function.Surjective j)
    (hf : f ≫ k = i ≫ f') (hg : g ≫ k = j ≫ g') :
    Function.Surjective (pullback.map f g f' g' i j k hf hg) := by
  have : IsIso (pullback.mapDesc f g k) := pullback_mapDesc_isIso f g k
  have : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  have h : Surjective (pullback.map (f ≫ k) (g ≫ k) f' g' i j (𝟙 _) (by simpa using hf)
      (by simpa using hg)) :=
    MorphismProperty.pullbackMap (P := @Surjective) ⟨hi⟩ ⟨hj⟩ hf hg
  have heq : pullback.map f g f' g' i j k hf hg =
      pullback.mapDesc f g k ≫
        pullback.map (f ≫ k) (g ≫ k) f' g' i j (𝟙 _) (by simpa using hf)
          (by simpa using hg) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback_mapDesc_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback_mapDesc_snd]
  rw [heq]
  exact Surjective.surj (f := _)

/-- The first projection of the closed immersion of the underlying scheme of a fibre product of
divided power schemes into the ordinary fibre product. -/
private theorem underlyingPullbackComparison_fst {T T' R : DividedPowerScheme.{u}} (f : T ⟶ R)
    (f' : T' ⟶ R) :
    DividedPowerScheme.underlyingPullbackComparison f f' ≫ pullback.fst f.hom f'.hom =
      (pullback.fst f f').hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the closed immersion of the underlying scheme of a fibre product of
divided power schemes into the ordinary fibre product. -/
private theorem underlyingPullbackComparison_snd {T T' R : DividedPowerScheme.{u}} (f : T ⟶ R)
    (f' : T' ⟶ R) :
    DividedPowerScheme.underlyingPullbackComparison f f' ≫ pullback.snd f.hom f'.hom =
      (pullback.snd f f').hom :=
  pullback.lift_snd _ _ _

/-- **Maps into the underlying scheme of a fibre product of divided power schemes are determined
by their two projections.**  The underlying scheme of the divided power fibre product is a closed
subscheme of the ordinary fibre product of the underlying schemes,
`Crystalline.DividedPowerScheme.underlyingPullbackComparison_isClosedImmersion`, so the comparison
is a monomorphism and the two projections may be compared there. -/
theorem pullbackUnderlying_hom_ext {T T' R : DividedPowerScheme.{u}} (f : T ⟶ R) (f' : T' ⟶ R)
    {Z : Scheme.{u}} {h k : Z ⟶ (pullback f f').scheme}
    (hfst : h ≫ (pullback.fst f f').hom = k ≫ (pullback.fst f f').hom)
    (hsnd : h ≫ (pullback.snd f f').hom = k ≫ (pullback.snd f f').hom) : h = k := by
  have := DividedPowerScheme.underlyingPullbackComparison_isClosedImmersion f f'
  refine (cancel_mono (DividedPowerScheme.underlyingPullbackComparison f f')).mp ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, underlyingPullbackComparison_fst]
    exact hfst
  · rw [Category.assoc, Category.assoc, underlyingPullbackComparison_snd]
    exact hsnd

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The identification of the thickened scheme with the closed fibre is natural.**  Both sides
become the closed fibre inclusion of the source composed with the map on ambient schemes after
composing with the immersion of the target, which is a monomorphism. -/
theorem closedFiberSourceIso_naturality {A B : Thickening S} (f : A ⟶ B) :
    DividedPowerScheme.closedFiberMap f.targetHom ≫ B.thickening.closedFiberSourceIso.hom =
      A.thickening.closedFiberSourceIso.hom ≫ f.sourceHom := by
  refine (cancel_mono B.thickening.immersion).mp ?_
  calc
    (DividedPowerScheme.closedFiberMap f.targetHom ≫
          B.thickening.closedFiberSourceIso.hom) ≫ B.thickening.immersion
        = DividedPowerScheme.closedFiberι A.thickening.target ≫ f.targetHom.hom := by
      rw [Category.assoc, SchemeThickening.closedFiberSourceIso_hom_immersion,
        DividedPowerScheme.closedFiberMap_comp_closedFiberι]
    _ = (A.thickening.closedFiberSourceIso.hom ≫ f.sourceHom) ≫ B.thickening.immersion := by
      rw [Category.assoc, ← f.immersion_naturality, ← Category.assoc,
        SchemeThickening.closedFiberSourceIso_hom_immersion]

section Pullback

variable {A B C : Thickening S} (f : A ⟶ C) (g : B ⟶ C)

/-- **The closed fibre of the fibre product of the ambient divided power schemes is the fibre
product of the thickened schemes.**  The closed fibre of a fibre product of divided power schemes
is the fibre product of the closed fibres, [Stacks, Tag 07ME], and each closed fibre is the
corresponding thickened scheme by `Crystalline.SchemeThickening.closedFiberSourceIso`. -/
def pullbackClosedFiberSourceIso :
    DividedPowerScheme.closedFiber (pullback f.targetHom g.targetHom) ≅
      pullback f.sourceHom g.sourceHom :=
  haveI := DividedPowerScheme.closedFiberPullbackComparison_isIso f.targetHom g.targetHom
  asIso (DividedPowerScheme.closedFiberPullbackComparison f.targetHom g.targetHom) ≪≫
    asIso (pullback.map _ _ f.sourceHom g.sourceHom
      A.thickening.closedFiberSourceIso.hom B.thickening.closedFiberSourceIso.hom
      C.thickening.closedFiberSourceIso.hom
      (closedFiberSourceIso_naturality f) (closedFiberSourceIso_naturality g))

/-- The identification of the closed fibre with the fibre product of thickened schemes, as a
composite of the two comparison maps it is built from. -/
private theorem pullbackClosedFiberSourceIso_hom :
    (pullbackClosedFiberSourceIso f g).hom =
      DividedPowerScheme.closedFiberPullbackComparison f.targetHom g.targetHom ≫
        pullback.map _ _ f.sourceHom g.sourceHom
          A.thickening.closedFiberSourceIso.hom B.thickening.closedFiberSourceIso.hom
          C.thickening.closedFiberSourceIso.hom
          (closedFiberSourceIso_naturality f) (closedFiberSourceIso_naturality g) :=
  rfl

/-- The identification of the closed fibre with the fibre product of thickened schemes commutes
with the first projection. -/
theorem pullbackClosedFiberSourceIso_hom_fst :
    (pullbackClosedFiberSourceIso f g).hom ≫ pullback.fst f.sourceHom g.sourceHom =
      DividedPowerScheme.closedFiberMap (pullback.fst f.targetHom g.targetHom) ≫
        A.thickening.closedFiberSourceIso.hom := by
  rw [pullbackClosedFiberSourceIso_hom, Category.assoc, pullback.lift_fst, ← Category.assoc,
    DividedPowerScheme.closedFiberPullbackComparison_fst]

/-- The identification of the closed fibre with the fibre product of thickened schemes commutes
with the second projection. -/
theorem pullbackClosedFiberSourceIso_hom_snd :
    (pullbackClosedFiberSourceIso f g).hom ≫ pullback.snd f.sourceHom g.sourceHom =
      DividedPowerScheme.closedFiberMap (pullback.snd f.targetHom g.targetHom) ≫
        B.thickening.closedFiberSourceIso.hom := by
  rw [pullbackClosedFiberSourceIso_hom, Category.assoc, pullback.lift_snd, ← Category.assoc,
    DividedPowerScheme.closedFiberPullbackComparison_snd]

/-- **The immersion of the fibre product in `CRIS(X/S)`**: the fibre product of the thickened
schemes, identified with the closed fibre of the fibre product of the ambient divided power
schemes, included into the latter. -/
def pullbackImmersion :
    pullback f.sourceHom g.sourceHom ⟶ (pullback f.targetHom g.targetHom).scheme :=
  (pullbackClosedFiberSourceIso f g).inv ≫
    DividedPowerScheme.closedFiberι (pullback f.targetHom g.targetHom)

/-- The immersion of the fibre product is compatible with a pair of maps out of the fibre products
which commute with the identifications of the thickened schemes with the closed fibres. -/
private theorem pullbackImmersion_comp_hom {D : SchemeThickening.{u}}
    (Q : pullback f.targetHom g.targetHom ⟶ D.target)
    (P : pullback f.sourceHom g.sourceHom ⟶ D.source)
    (h : (pullbackClosedFiberSourceIso f g).hom ≫ P =
      DividedPowerScheme.closedFiberMap Q ≫ D.closedFiberSourceIso.hom) :
    pullbackImmersion f g ≫ Q.hom = P ≫ D.immersion := by
  refine (cancel_epi (pullbackClosedFiberSourceIso f g).hom).mp ?_
  simp only [pullbackImmersion, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← DividedPowerScheme.closedFiberMap_comp_closedFiberι,
    ← SchemeThickening.closedFiberSourceIso_hom_immersion, ← Category.assoc, ← h]

/-- The immersion of the fibre product is compatible with the first projections. -/
theorem pullbackImmersion_fst :
    pullbackImmersion f g ≫ (pullback.fst f.targetHom g.targetHom).hom =
      pullback.fst f.sourceHom g.sourceHom ≫ A.thickening.immersion :=
  pullbackImmersion_comp_hom f g _ _ (pullbackClosedFiberSourceIso_hom_fst f g)

/-- The immersion of the fibre product is compatible with the second projections. -/
theorem pullbackImmersion_snd :
    pullbackImmersion f g ≫ (pullback.snd f.targetHom g.targetHom).hom =
      pullback.snd f.sourceHom g.sourceHom ≫ B.thickening.immersion :=
  pullbackImmersion_comp_hom f g _ _ (pullbackClosedFiberSourceIso_hom_snd f g)

/-- **The immersion of the fibre product is a thickening.**  It is a closed immersion because it is
the closed fibre inclusion precomposed with an isomorphism.  For surjectivity, its composite with
the closed immersion of the underlying scheme of the divided power fibre product into the ordinary
fibre product is the map of ordinary fibre products induced by the three immersions, which is
surjective by `Crystalline.pullback_map_surjective`; surjectivity of a composite with a closed
immersion gives surjectivity of the first factor. -/
theorem pullbackImmersion_isThickening : IsThickening (pullbackImmersion f g) := by
  have : IsClosedImmersion (pullbackImmersion f g) :=
    show IsClosedImmersion ((pullbackClosedFiberSourceIso f g).inv ≫
      DividedPowerScheme.closedFiberι (pullback f.targetHom g.targetHom)) from inferInstance
  refine ⟨inferInstance, ?_⟩
  have := DividedPowerScheme.underlyingPullbackComparison_isClosedImmersion
    f.targetHom g.targetHom
  have heq : pullbackImmersion f g ≫
      DividedPowerScheme.underlyingPullbackComparison f.targetHom g.targetHom =
      pullback.map f.sourceHom g.sourceHom f.targetHom.hom g.targetHom.hom
        A.thickening.immersion B.thickening.immersion C.thickening.immersion
        f.immersion_naturality.symm g.immersion_naturality.symm := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, underlyingPullbackComparison_fst, pullback.lift_fst]
      exact pullbackImmersion_fst f g
    · rw [Category.assoc, underlyingPullbackComparison_snd, pullback.lift_snd]
      exact pullbackImmersion_snd f g
  have hs : Function.Surjective (pullbackImmersion f g ≫
      DividedPowerScheme.underlyingPullbackComparison f.targetHom g.targetHom) := by
    rw [heq]
    exact pullback_map_surjective _ _ _ _ _ _ _
      A.thickening.isThickening.2 B.thickening.isThickening.2 _ _
  intro x
  obtain ⟨y, hy⟩ := hs (DividedPowerScheme.underlyingPullbackComparison
    f.targetHom g.targetHom x)
  exact ⟨y, (DividedPowerScheme.underlyingPullbackComparison
    f.targetHom g.targetHom).isClosedEmbedding.injective hy⟩

/-- **The divided power ideal of the fibre product of the ambient divided power schemes is the
ideal of the immersion of the fibre product.**  The immersion differs from the closed fibre
inclusion by an isomorphism, which does not change the ideal sheaf. -/
theorem pullbackImmersion_ideal
    (V : (pullback f.targetHom g.targetHom).scheme.affineOpens) :
    (pullback f.targetHom g.targetHom).ideal.obj (op (V : _)) =
      (pullbackImmersion f g).ker.ideal V := by
  have hker : (pullbackImmersion f g).ker =
      (DividedPowerScheme.closedFiberι (pullback f.targetHom g.targetHom)).ker :=
    Scheme.Hom.ker_comp_of_isIso _ _
  rw [hker, ker_ideal_closedFiberι]

/-- **The fibre product of two morphisms of `CRIS(X/S)`**: the fibre products of the thickened
schemes and of the ambient divided power schemes, with the immersion between them of
`Crystalline.GlobalCrystallineSituation.pullbackImmersion`, over the divided power base and over
`X` through the first projection. -/
def pullbackObject : Thickening S where
  thickening :=
    { source := pullback f.sourceHom g.sourceHom
      target := pullback f.targetHom g.targetHom
      immersion := pullbackImmersion f g
      isThickening := pullbackImmersion_isThickening f g
      ideal_eq_ker := pullbackImmersion_ideal f g }
  toBase := pullback.fst f.targetHom g.targetHom ≫ A.toBase
  toX := pullback.fst f.sourceHom g.sourceHom ≫ A.toX
  over_base := by
    change pullbackImmersion f g ≫
      ((pullback.fst f.targetHom g.targetHom).hom ≫ A.toBase.hom) = _
    rw [← Category.assoc, pullbackImmersion_fst, Category.assoc, A.over_base, Category.assoc]

/-- The first projection of the fibre product of `CRIS(X/S)`. -/
def pullbackFst : pullbackObject f g ⟶ A where
  sourceHom := pullback.fst _ _
  targetHom := pullback.fst _ _
  immersion_naturality := pullbackImmersion_fst f g
  base_naturality := rfl
  toX_naturality := rfl

/-- The second projection of the fibre product of `CRIS(X/S)`.  Its compatibilities with the maps
to the divided power base and to `X` are the compatibility of the two projections of the
underlying fibre products. -/
def pullbackSnd : pullbackObject f g ⟶ B where
  sourceHom := pullback.snd _ _
  targetHom := pullback.snd _ _
  immersion_naturality := pullbackImmersion_snd f g
  base_naturality := by
    change pullback.snd f.targetHom g.targetHom ≫ B.toBase =
      pullback.fst f.targetHom g.targetHom ≫ A.toBase
    rw [← f.base_naturality, ← g.base_naturality, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  toX_naturality := by
    change pullback.snd f.sourceHom g.sourceHom ≫ B.toX =
      pullback.fst f.sourceHom g.sourceHom ≫ A.toX
    rw [← f.toX_naturality, ← g.toX_naturality, ← Category.assoc, ← Category.assoc,
      pullback.condition]

/-- The square defining the fibre product of `CRIS(X/S)` commutes. -/
theorem pullback_condition : pullbackFst f g ≫ f = pullbackSnd f g ≫ g := by
  refine Thickening.Hom.ext ?_ ?_
  · exact pullback.condition
  · exact pullback.condition

/-- **The lift of a cone over the fibre product square of `CRIS(X/S)`**, assembled from the lifts
of the two underlying fibre products.  The commuting square of thickenings is checked after the
closed immersion into the ordinary fibre product of the underlying schemes,
`Crystalline.pullbackUnderlying_hom_ext`. -/
def pullbackLift (s : PullbackCone f g) : s.pt ⟶ pullbackObject f g where
  sourceHom := pullback.lift s.fst.sourceHom s.snd.sourceHom
    (congrArg (fun k ↦ k.sourceHom) s.condition)
  targetHom := pullback.lift s.fst.targetHom s.snd.targetHom
    (congrArg (fun k ↦ k.targetHom) s.condition)
  immersion_naturality := by
    dsimp only [pullbackObject]
    refine pullbackUnderlying_hom_ext f.targetHom g.targetHom ?_ ?_
    · rw [Category.assoc, ← DividedPowerScheme.Hom.comp_hom, pullback.lift_fst, Category.assoc,
        pullbackImmersion_fst, ← Category.assoc, pullback.lift_fst]
      exact s.fst.immersion_naturality
    · rw [Category.assoc, ← DividedPowerScheme.Hom.comp_hom, pullback.lift_snd, Category.assoc,
        pullbackImmersion_snd, ← Category.assoc, pullback.lift_snd]
      exact s.snd.immersion_naturality
  base_naturality := by
    change _ ≫ (pullback.fst f.targetHom g.targetHom ≫ A.toBase) = _
    rw [← Category.assoc, pullback.lift_fst, s.fst.base_naturality]
  toX_naturality := by
    change _ ≫ (pullback.fst f.sourceHom g.sourceHom ≫ A.toX) = _
    rw [← Category.assoc, pullback.lift_fst, s.fst.toX_naturality]

/-- The lift of a cone is compatible with the first projection. -/
theorem pullbackLift_fst (s : PullbackCone f g) :
    pullbackLift f g s ≫ pullbackFst f g = s.fst := by
  refine Thickening.Hom.ext ?_ ?_
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_fst _ _ _

/-- The lift of a cone is compatible with the second projection. -/
theorem pullbackLift_snd (s : PullbackCone f g) :
    pullbackLift f g s ≫ pullbackSnd f g = s.snd := by
  refine Thickening.Hom.ext ?_ ?_
  · exact pullback.lift_snd _ _ _
  · exact pullback.lift_snd _ _ _

/-- Morphisms into the fibre product of `CRIS(X/S)` are determined by their two projections. -/
theorem pullback_hom_ext {Z : Thickening S} {h k : Z ⟶ pullbackObject f g}
    (hfst : h ≫ pullbackFst f g = k ≫ pullbackFst f g)
    (hsnd : h ≫ pullbackSnd f g = k ≫ pullbackSnd f g) : h = k := by
  refine Thickening.Hom.ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
  · exact congrArg (fun q ↦ q.sourceHom) hfst
  · exact congrArg (fun q ↦ q.sourceHom) hsnd
  · exact congrArg (fun q ↦ q.targetHom) hfst
  · exact congrArg (fun q ↦ q.targetHom) hsnd

/-- The fibre product of two morphisms of `CRIS(X/S)` exists. -/
theorem hasPullback_thickening : HasPullback f g := by
  refine HasLimit.mk ⟨PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (pullback_condition f g),
      PullbackCone.IsLimit.mk _ (pullbackLift f g) (pullbackLift_fst f g)
        (pullbackLift_snd f g) ?_⟩
  intro s m hm₁ hm₂
  refine pullback_hom_ext f g ?_ ?_
  · rw [hm₁, pullbackLift_fst]
  · rw [hm₂, pullbackLift_snd]

end Pullback

/-- **Stacks Project, Tag 07I9, part of the first assertion.** The big crystalline category
`CRIS(X/S)` has fibre products: the fibre product of the ambient divided power schemes,
[Stacks, Tag 07ME], is the ambient divided power scheme of the fibre product, and its closed
fibre is the fibre product of the thickened schemes.

This is the fibre product half of the first assertion of [Stacks, Tag 07I9], proved directly from
the envelope rather than deduced from binary products.  Clause (1) in full is
`Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening` in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductInstance.lean`. -/
@[stacks 07I9 "part of clause (1): fibre products, built directly from the envelope of 07ME"]
instance instHasPullbacksThickening (S : GlobalCrystallineSituation.{u}) :
    HasPullbacks (Thickening S) := by
  have {A B C : Thickening S} {f : A ⟶ C} {g : B ⟶ C} : HasPullback f g :=
    hasPullback_thickening f g
  exact hasPullbacks_of_hasLimit_cospan _

end GlobalCrystallineSituation

end Crystalline

end
