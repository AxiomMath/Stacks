module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing the direct images of [Stacks, Tag 07Q9]

[Stacks, Tag 07Q9] reduces to the chain `X' = X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0 = X` of `α_p`-covers
whose composite is the given iterated `α_p`-cover, proves that each stage contributes a cone
annihilated by `p`, and invokes (TR 4) to multiply the annihilators into `p ^ n = q` for the
composite.  Two things are needed to run that reduction against the statement
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07Q9` of
`SmallSite/AlphaPCoverTriangle.lean`:

1. **(TR 4) in the shape of 07Q9's own conclusion** — the annihilators of `Annihilation07Q9`
   multiply along a composition.  This is proved here, unconditionally, as
   `annihilation07Q9_comp`.
2. **The comparison map of a composite cover is the composite of the comparison maps** — the
   *composition functoriality* of `derivedZariskiComparison`.  This file builds every part of it
   that is not genuine crystalline geometry and isolates the part that is.  Each of the three
   factors of `f_{cris, *}` is treated separately, and the one that is genuine geometry —
   `HasCrisDirectImageComp` below — is a theorem of
   `SmallSite/CrisDirectImageCompositionIso.lean`.

Throughout, the situations are written `S₂ ⟶ S₁ ⟶ S₀`, so that `f₁ : X₂ ⟶ X₁` and `f₂ : X₁ ⟶ X₀`
and the composite is `f₁ ≫ f₂`; the orientation matches `SmallSite/CrisDirectImage.lean`, where
the first argument of `crisDirectImage` is the source situation.

## What is proved, unconditionally

* **Composition of cocontinuous pushforwards in general.**  `Stacks.Sites`
  `.sheafPushforwardCocontinuousComp`: for continuous and cocontinuous functors of sites with
  `F ⋙ G ≅ FG`, the cocontinuous pushforwards compose.  No limit comparison is computed — the
  cocontinuous pushforward is the right adjoint of the continuous one, the continuous one composes
  on the nose (`CategoryTheory.Functor.sheafPushforwardContinuousComp'`), and right adjoints are
  determined by their left adjoints.  This is the engine of the whole file.
* **Change of divided power base is functorial**, `changeBaseComp`, and the square of closed
  fibres of [Stacks, Tag 07MJ] pastes, `comp_closedFiber_compat`.  The isomorphism of functors of
  sites is the identity on the underlying divided power thickenings; it fails to be an equality
  only because an object's structure morphisms are composed in the two possible bracketings.
* **`f_{CRIS, *}` is functorial**, `changeBaseDirectImageComp`, from the previous two.
* **The big-site half of `f_{cris, *}` is a single right Kan extension**,
  `bigDirectImageChangeBaseIso`: `i_{X₂, *}` followed by `f₁_{CRIS, *}` is the cocontinuous
  pushforward along the one functor of sites `Cris(X₂/S₂) ⥤ CRIS(X₁/S₁)`.
* **`f_{Zar, *}` and `Rf_{Zar, *}` are functorial**, `zariskiPushforwardComp` and
  `derivedZariskiPushforwardComp`.  The underived statement is `TopologicalSpace.Opens.mapComp`
  read through `sheafPushforwardContinuousComp'`; the derived statement is the comparison of
  [Stacks, Tag 015M], invertible because `f_{Zar, *}` preserves injective abelian sheaves
  (`preservesInjectiveObjects_zariskiPushforward`).  **This is the `f_*` of 07Q9's
  triangle, and its composition functoriality is now a theorem of this library.**
* **The canonical comparison `f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}`**,
  `crisDirectImageCompCell`, with its value on a sheaf, `crisDirectImageCompCell_app`.
* **(TR 4) for `Annihilation07Q9`**, `annihilation07Q9_comp`.  The two triangulated inputs it
  rests on are also proved, in `Crystalline/AlphaPCoverCohomologyBound.lean`:
  `Stacks.Triangulated.mul_smul_id_eq_zero_of_exact`, that annihilators multiply along an exact
  sequence, and `Stacks.Triangulated.mul_smul_id_homologyFunctor_eq_zero_of_comp`, the octahedron
  axiom followed by the cohomology long exact sequence.

## The comparison, and where its invertibility is proved

`f_{cris, *}` is by definition the composite `π_{X, *} ∘ f_{CRIS, *} ∘ i_{X, *}` of
[Stacks, Tag 07IK].  Composing two of these leaves one occurrence of `i_{X₁, *} ∘ π_{X₁, *}` in
the middle, between the two halves of `f_{CRIS, *}` that `changeBaseDirectImageComp` identifies.
So the comparison between `f_{cris, *}` for the composite and the composite of the two
`f_{cris, *}` is the **unit** of `π_{X₁, *} ⊣ i_{X₁, *}`, whiskered into place, and it is written
in that one direction: [Stacks, Tag 07IJ] gives `π_{X, *} ∘ i_{X, *} = id`, which is the *counit*
`i_{X}^{-1}i_{X, *} ≅ 𝟭` and says nothing about the unit.  Hence

* `crisDirectImageCompCell` is built here as a natural transformation;
* `HasCrisDirectImageComp` is the assertion that it is an isomorphism; and
* `hasCrisDirectImageComp_of_isIso_unit` is one sufficient condition for it — that the unit
  `H ⟶ i_{X₁, *}π_{X₁, *}H` be invertible as a map of sheaves on the *big* site `CRIS(X₁/S₁)` at
  the sheaves `H = f₁_{CRIS, *}i_{X₂, *}ℱ`.

That sufficient condition is stronger than the assertion: in `crisDirectImageCompCell` the unit
occurs only under `π_{X₀, *}f₂_{CRIS, *}`, which reads it at the objects of the *small* site
`Cris(X₀/S₀)` alone.  `SmallSite/CrisDirectImageCompositionIso.lean` proves
`HasCrisDirectImageComp` at that sharper measure, `...SmallSite.hasCrisDirectImageComp`, from
`...SmallSite.isIso_smallRestriction_changeBase_unit` of `SmallSite/SmallTargetUnitIso.lean`.

Read through `bigDirectImageChangeBaseIso` the invertibility is a concrete limit comparison.  At an
object `A` of `CRIS(X₁/S₁)` it asks for

`lim_{(C, f₁_{CRIS}(i_{X₂}C) ⟶ A)} ℱ(C)`
  `⟶ lim_{(B, i_{X₁}B ⟶ A)} lim_{(C, f₁_{CRIS}(i_{X₂}C) ⟶ i_{X₁}B)} ℱ(C)`

to be invertible, `C` ranging over `Cris(X₂/S₂)` and `B` over `Cris(X₁/S₁)`; equivalently, for the
projection from the dominating pairs to be initial.  Its comma categories are nonempty exactly
when an object `C` of `Cris(X₂/S₂)` together with a morphism `f₁_{CRIS}(i_{X₂}C) ⟶ A` can be
dominated by an object of the *small* site `Cris(X₁/S₁)` compatibly over `A` — i.e. when the
divided power thickening of an open of `X₂` embeds in one of an open of `X₁`.  That is the same
shape as the obstruction (★) of `SmallSite/StructureMorphism.lean`, and as there the route is not
cofinality — which is false in general — but the **sheaf condition**: shrink `C` to affine
refinements, dominate each by the pushout of [Stacks, Tag 07RT], and amalgamate over the resulting
covering sieve.  `SmallSite/SmallTargetDomination.lean` carries out the covering and independence
steps of that domination when `A` lies in the small site, and
`SmallSite/SmallTargetUnitIso.lean` assembles them into the inverse, exactly as the three files
`SmallSite/CrisZariskiSquare{Covering, Limit, Iso}.lean` do for the square of topoi of
[Stacks, Tag 07Q9].

**No tag attribute is placed in this file.**  Nothing here proves a clause of [Stacks, Tag 07Q9]:
`HasCrisDirectImageComp` is a definition of a proposition, in the manner of `Statement07Q9`.

## What [Stacks, Tag 07Q9] still owes

With this file and `SmallSite/CrisDirectImageCompositionIso.lean` in place the composition
functoriality of `derivedZariskiComparison` — "the comparison map of `f₁ ≫ f₂` is the comparison
map of `f₂` followed by `Rf₂_{Zar, *}` of the comparison map of `f₁`" — needs exactly three
inputs, of which the second and third are *not* addressed here:

1. `HasCrisDirectImageComp`, discussed above, and through it the derived statement
   `derivedCrisDirectImageComp`, which this file deduces from it.  Both are theorems of this
   library: `...SmallSite.hasCrisDirectImageComp` and
   `...SmallSite.derivedCrisDirectImageCompIso` of
   `SmallSite/CrisDirectImageCompositionIso.lean`.
2. The mirror composition of the crystalline *inverse* image, `crisPullback S₂ S₁ ∘
   crisPullback S₁ S₀ ≅ crisPullback S₂ S₀`.  It is the left-adjoint mirror of 1, and it is a
   theorem of this library: `...SmallSite.crisInverseImageComp` and
   `...SmallSite.crisPullbackComp` of `SmallSite/CrisInverseImageComposition.lean`, with the
   compatibility of the units `...SmallSite.crisUnit_comp_eq` that the comparison map needs.
   Its mirror obstruction — `π_{X₁, *}` followed by `i_{X₁, !}` in the middle, whose comparison
   is the *counit* of `i_{X₁, !} ⊣ π_{X₁, *}` — is never met head on: both sides are left
   adjoints of the two sides of 1, and `CategoryTheory.conjugateEquiv` carries the isomorphism
   of 1 to one of them.
3. The coherence of the three commutation data: that the term `...SmallSite.crisZariskiSquare`
   for `f₁ ≫ f₂` is the pasting of those for `f₁` and for `f₂` across
   `zariskiPushforwardComp`.  This does not follow from 1 and 2; it is a statement about the
   specific square built in `SmallSite/CrisZariskiSquareIso.lean`, and it is stated as
   `...SmallSite.CrisZariskiCellComp` of `SmallSite/CrisZariskiSquareComposition.lean` and proved
   as `...SmallSite.crisZariskiCellComp` of
   `SmallSite/CrisZariskiCellCompositionProof.lean`.  The first module derives from it, and from
   1 and 2, that the comparison map of `f₁ ≫ f₂` is the comparison map of `f₂` followed by
   `f₂_{Zar, *}` of the comparison map of `f₁`, `...SmallSite.zariskiComparison_comp`.

Beyond the composition functoriality, [Stacks, Tag 07Q9] owes the *local* step — that one
`α_p`-cover contributes a cone annihilated by `p` — which is [Stacks, Proposition 07LG] together
with [Stacks, Tag 07Q7] at `a = p` (`Crystalline.exists_homotopyInverse_pthRootExtension`),
and the passage from `p ^ n` to the constant degree `q`, which is
`Crystalline/AlphaPCoverDegree.lean`.

## References

* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Stacks.Sites

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {A : Type*} [Category A]
  {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)
  [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
  [F.IsCocontinuous J K] [G.IsCocontinuous K L] [FG.IsCocontinuous J L]
  [∀ (P : Cᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension P]
  [∀ (P : Dᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension P]
  [∀ (P : Cᵒᵖ ⥤ A), FG.op.HasPointwiseRightKanExtension P]

/-- **The pushforward along a cocontinuous functor of sites composes.**  Given continuous and
cocontinuous functors of sites `F : (C, J) ⥤ (D, K)` and `G : (D, K) ⥤ (E, L)` and an isomorphism
`F ⋙ G ≅ FG`, the composite of the cocontinuous pushforwards is the cocontinuous pushforward
along `FG`.

No limit comparison is computed: the cocontinuous pushforward is the *right adjoint* of the
continuous one by `CategoryTheory.Functor.sheafAdjunctionCocontinuous`, the continuous one
composes on the nose by `CategoryTheory.Functor.sheafPushforwardContinuousComp'`, and a right
adjoint is determined up to canonical isomorphism by its left adjoint. -/
@[sga "4 III 4.4" "special case", sga "4 IV 4.7" "special case"]
def sheafPushforwardCocontinuousComp :
    F.sheafPushforwardCocontinuous A J K ⋙ G.sheafPushforwardCocontinuous A K L ≅
      FG.sheafPushforwardCocontinuous A J L :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft
      ((G.sheafAdjunctionCocontinuous A K L).comp (F.sheafAdjunctionCocontinuous A J K))
      (Functor.sheafPushforwardContinuousComp' (A := A) e J K L))
    (FG.sheafAdjunctionCocontinuous A J L)

end Stacks.Sites

namespace Crystalline.GlobalCrystallineSituation

variable {S₂ S₁ S₀ : GlobalCrystallineSituation.{u}}
  {f₁S : S₂.S ⟶ S₁.S} {f₁X : S₂.X ⟶ S₁.X}
  {f₂S : S₁.S ⟶ S₀.S} {f₂X : S₁.X ⟶ S₀.X}

/-- **The square of closed fibres of [Stacks, Tag 07MJ] composes.**  If `f₁` and `f₂` are
morphisms of global crystalline situations then so is their composite: the compatibility of the
structure morphisms to the closed fibres is the pasting of the two squares, the closed fibre
being functorial (`Crystalline.DividedPowerScheme.closedFiberMap_comp`). -/
theorem comp_closedFiber_compat
    (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
    (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber) :
    S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap (f₁S ≫ f₂S) =
      (f₁X ≫ f₂X) ≫ S₀.toClosedFiber := by
  rw [DividedPowerScheme.closedFiberMap_comp, ← Category.assoc, h₁, Category.assoc, h₂,
    Category.assoc]

variable
  (h₁ : S₂.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₁S = f₁X ≫ S₁.toClosedFiber)
  (h₂ : S₁.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f₂S = f₂X ≫ S₀.toClosedFiber)

/-- The comparison morphism of the two readings of a rebased object: rebasing along `f₁` and then
along `f₂` leaves the divided power thickening alone and composes the structure morphisms, which
is what rebasing along `f₁ ≫ f₂` does, so the identity of the underlying thickening is a
morphism of `CRIS(X₀/S₀)` between them. -/
def changeBaseCompHom (A : Thickening S₂) :
    (changeBase S₂ S₁ f₁S f₁X h₁ ⋙ changeBase S₁ S₀ f₂S f₂X h₂).obj A ⟶
      (changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)).obj A where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := by simp
  base_naturality := by simp
  toX_naturality := by simp

/-- The inverse of `changeBaseCompHom`, again the identity of the underlying thickening. -/
def changeBaseCompInv (A : Thickening S₂) :
    (changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂)).obj A ⟶
      (changeBase S₂ S₁ f₁S f₁X h₁ ⋙ changeBase S₁ S₀ f₂S f₂X h₂).obj A where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := by simp
  base_naturality := by simp
  toX_naturality := by simp

/-- **Change of divided power base is functorial**, [Stacks, Tag 07IC]: rebasing along `f₁` and
then along `f₂` is rebasing along `f₁ ≫ f₂`.  The isomorphism is the identity on the underlying
divided power thickenings; it is not an equality of functors only because the structure morphisms
of an object are composed in the two possible bracketings. -/
def changeBaseComp :
    changeBase S₂ S₁ f₁S f₁X h₁ ⋙ changeBase S₁ S₀ f₂S f₂X h₂ ≅
      changeBase S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) :=
  NatIso.ofComponents
    (fun A ↦
      { hom := changeBaseCompHom h₁ h₂ A
        inv := changeBaseCompInv h₁ h₂ A
        hom_inv_id := by apply Thickening.Hom.ext <;> simp [changeBaseCompHom, changeBaseCompInv]
        inv_hom_id := by apply Thickening.Hom.ext <;> simp [changeBaseCompHom, changeBaseCompInv] })
    (fun k ↦ by apply Thickening.Hom.ext <;> simp [changeBaseCompHom])

namespace SmallSite

/-- **`f_{CRIS, *}` is functorial in the morphism of situations**: the direct image on abelian
sheaves of the big crystalline sites along `f₁` followed by that along `f₂` is the one along
`f₁ ≫ f₂`.  Unconditional, and no limit is computed: `changeBaseDirectImage` is the cocontinuous
pushforward, `changeBaseComp` is the composition of the functors of sites, and
`Stacks.Sites.sheafPushforwardCocontinuousComp` turns the one into the other. -/
def changeBaseDirectImageComp :
    changeBaseDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ changeBaseDirectImage S₁ S₀ f₂S f₂X h₂ ≅
      changeBaseDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) :=
  Stacks.Sites.sheafPushforwardCocontinuousComp (A := AddCommGrpCat.{u + 1})
    (changeBaseComp h₁ h₂) (topology S₂) (topology S₁) (topology S₀)

/-- The composite functor of sites `Cris(X₂/S₂) ⥤ CRIS(X₁/S₁)` is continuous, both factors
being so. -/
instance isContinuous_ι_comp_changeBase :
    (CrystallineThickening.ι S₂ ⋙ changeBase S₂ S₁ f₁S f₁X h₁).IsContinuous
      (smallTopology S₂) (topology S₁) :=
  Functor.isContinuous_comp _ _ _ (topology S₂) _

/-- The composite functor of sites `Cris(X₂/S₂) ⥤ CRIS(X₁/S₁)` is cocontinuous, both factors
being so. -/
instance isCocontinuous_ι_comp_changeBase :
    (CrystallineThickening.ι S₂ ⋙ changeBase S₂ S₁ f₁S f₁X h₁).IsCocontinuous
      (smallTopology S₂) (topology S₁) :=
  isCocontinuous_comp (CrystallineThickening.ι S₂) (changeBase S₂ S₁ f₁S f₁X h₁)
    (smallTopology S₂) (topology S₂)

/-- The right Kan extension along the composite functor of sites is computed by limits that
exist, exactly as for each factor: the index categories have objects in `Type (u + 1)` and
morphisms in `Type u`. -/
instance hasPointwiseRightKanExtension_ι_comp_changeBase
    (P : (CrystallineThickening S₂)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (CrystallineThickening.ι S₂ ⋙ changeBase S₂ S₁ f₁S f₁X h₁).op.HasPointwiseRightKanExtension
      P :=
  fun _ ↦ inferInstance

/-- **The big-site half of `f_{cris, *}` is a single right Kan extension.**  `i_{X₂, *}` followed
by `f₁_{CRIS, *}` is the cocontinuous pushforward along the one functor of sites
`Cris(X₂/S₂) ⥤ CRIS(X₁/S₁)`, so the sections of `f₁_{CRIS, *}i_{X₂, *}ℱ` over an object `A` of
`CRIS(X₁/S₁)` are the limit of `ℱ` over the objects `C` of `Cris(X₂/S₂)` equipped with a morphism
`f₁_{CRIS}(i_{X₂}C) ⟶ A`, with no intermediate limit.

This is what makes `HasCrisDirectImageComp` a concrete limit comparison; see the module
documentation. -/
def bigDirectImageChangeBaseIso :
    bigDirectImage S₂ ⋙ changeBaseDirectImage S₂ S₁ f₁S f₁X h₁ ≅
      (CrystallineThickening.ι S₂ ⋙ changeBase S₂ S₁ f₁S f₁X h₁).sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (smallTopology S₂) (topology S₁) :=
  Stacks.Sites.sheafPushforwardCocontinuousComp (A := AddCommGrpCat.{u + 1})
    (Iso.refl (CrystallineThickening.ι S₂ ⋙ changeBase S₂ S₁ f₁S f₁X h₁))
    (smallTopology S₂) (topology S₂) (topology S₁)

/-- **The canonical comparison `f_{cris, *} ⟶ f₁_{cris, *} ∘ f₂_{cris, *}` for a composite
morphism of global crystalline situations**, where `f = f₁ ≫ f₂`.

`f_{cris, *}` is the composite `π_{X, *} ∘ f_{CRIS, *} ∘ i_{X, *}` of [Stacks, Tag 07IK], and the
two sides of this comparison differ by exactly one occurrence of `i_{X₁, *} ∘ π_{X₁, *}` in the
middle, inserted between the two halves of `f_{CRIS, *}` which `changeBaseDirectImageComp`
identifies.  So the comparison is the unit of `π_{X₁, *} ⊣ i_{X₁, *}` — the adjunction
`bigDirectImageAdjunction` — whiskered into place, and it runs in the direction displayed and not
the other.

`HasCrisDirectImageComp` below is the assertion that it is an isomorphism, proved in
`SmallSite/CrisDirectImageCompositionIso.lean`. -/
def crisDirectImageCompCell :
    crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂) ⟶
      crisDirectImage S₂ S₁ f₁S f₁X h₁ ⋙ crisDirectImage S₁ S₀ f₂S f₂X h₂ :=
  Functor.whiskerLeft (bigDirectImage S₂)
    (Functor.whiskerRight
      ((changeBaseDirectImageComp h₁ h₂).inv ≫
        Functor.whiskerLeft (changeBaseDirectImage S₂ S₁ f₁S f₁X h₁)
          (Functor.whiskerRight (bigDirectImageAdjunction S₁).unit
            (changeBaseDirectImage S₁ S₀ f₂S f₂X h₂)))
      (smallRestriction S₀))

/-- The comparison of `crisDirectImageCompCell`, read on a sheaf: it is `π_{X₀, *}` of the
composition isomorphism of the big direct images followed by `f₂_{CRIS, *}` of the unit
`H ⟶ i_{X₁, *}π_{X₁, *}H` at `H = f₁_{CRIS, *}i_{X₂, *}ℱ`. -/
theorem crisDirectImageCompCell_app (F : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1}) :
    (crisDirectImageCompCell h₁ h₂).app F =
      (smallRestriction S₀).map
        ((changeBaseDirectImageComp h₁ h₂).inv.app ((bigDirectImage S₂).obj F) ≫
          (changeBaseDirectImage S₁ S₀ f₂S f₂X h₂).map
            ((bigDirectImageAdjunction S₁).unit.app
              ((changeBaseDirectImage S₂ S₁ f₁S f₁X h₁).obj ((bigDirectImage S₂).obj F)))) :=
  rfl

/-- **The assertion that `f_{cris, *}` is functorial in the morphism of situations**, for the
composite `f₁ ≫ f₂`: that `crisDirectImageCompCell` is invertible.

It is one of the three inputs the composition functoriality of the comparison map of
[Stacks, Tag 07Q9] needs, and it is a theorem:
`SmallSite/CrisDirectImageCompositionIso.lean` proves it as
`...SmallSite.hasCrisDirectImageComp`.  `hasCrisDirectImageComp_of_isIso_unit` below is one
sufficient condition for it, stronger than needed; see the module documentation. -/
def HasCrisDirectImageComp : Prop :=
  IsIso (crisDirectImageCompCell h₁ h₂)

/-- **One sufficient condition for the composition functoriality of `f_{cris, *}`.**  If the unit
`H ⟶ i_{X₁, *}π_{X₁, *}H` of `bigDirectImageAdjunction` is invertible — as a map of sheaves on the
big site `CRIS(X₁/S₁)` — at every sheaf of the form `H = f₁_{CRIS, *}i_{X₂, *}ℱ`, then
`HasCrisDirectImageComp` holds.

Everything else in `crisDirectImageCompCell` is already an isomorphism: the two outer factors are
functors, and the inner one is `changeBaseDirectImageComp`, which this file proves.

This asks more of the unit than `crisDirectImageCompCell` uses — there the unit occurs only under
`π_{X₀, *}f₂_{CRIS, *}`, which reads it at the objects of the small site `Cris(X₀/S₀)` alone — and
it is at that sharper measure that `...SmallSite.hasCrisDirectImageComp` of
`SmallSite/CrisDirectImageCompositionIso.lean` proves `HasCrisDirectImageComp`. -/
theorem hasCrisDirectImageComp_of_isIso_unit
    (hu : ∀ F : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1},
      IsIso ((bigDirectImageAdjunction S₁).unit.app
        ((changeBaseDirectImage S₂ S₁ f₁S f₁X h₁).obj ((bigDirectImage S₂).obj F)))) :
    HasCrisDirectImageComp h₁ h₂ := by
  have : ∀ F : Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1},
      IsIso ((crisDirectImageCompCell h₁ h₂).app F) := by
    intro F
    have := hu F
    rw [crisDirectImageCompCell_app]
    exact Functor.map_isIso _ _
  exact NatIso.isIso_of_isIso_app _

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S₀) AddCommGrpCat.{u + 1})]

/-- **`Rf_{cris, *}` is functorial in the morphism of situations**, from
`HasCrisDirectImageComp`.  The underived composition isomorphism is transported through the
comparison of [Stacks, Tag 05T2], which is invertible because `f₁_{cris, *}` preserves injective
abelian sheaves (`preservesInjectiveObjects_crisDirectImage`, unconditional).

`...SmallSite.derivedCrisDirectImageCompIso` of
`SmallSite/CrisDirectImageCompositionIso.lean` is this isomorphism with its argument supplied by
`...SmallSite.hasCrisDirectImageComp`. -/
def derivedCrisDirectImageComp (hcomp : HasCrisDirectImageComp h₁ h₂) :
    derivedCrisDirectImageFunctor S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X)
        (comp_closedFiber_compat h₁ h₂) ≅
      derivedCrisDirectImageFunctor S₂ S₁ f₁S f₁X h₁ ⋙
        derivedCrisDirectImageFunctor S₁ S₀ f₂S f₂X h₂ :=
  haveI : IsIso (crisDirectImageCompCell h₁ h₂) := hcomp
  Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso
    (crisDirectImage S₂ S₁ f₁S f₁X h₁) (crisDirectImage S₁ S₀ f₂S f₂X h₂)
    (crisDirectImage S₂ S₀ (f₁S ≫ f₂S) (f₁X ≫ f₂X) (comp_closedFiber_compat h₁ h₂))
    (asIso (crisDirectImageCompCell h₁ h₂)).symm

end Derived

/-! ### The Zariski direct image along the composite, unconditionally -/

/-- **`f_{Zar, *}` is functorial in `f`.**  Pushforward of abelian sheaves along the map of small
Zariski sites induced by `f₁ ≫ f₂` is pushforward along `f₁` followed by pushforward along `f₂`.
Unconditional: both sides are restriction along a continuous functor of sites and
`TopologicalSpace.Opens.mapComp` identifies the two functors. -/
def zariskiPushforwardComp :
    zariskiPushforward S₂ S₁ f₁X ⋙ zariskiPushforward S₁ S₀ f₂X ≅
      zariskiPushforward S₂ S₀ (f₁X ≫ f₂X) :=
  Functor.sheafPushforwardContinuousComp' (A := AddCommGrpCat.{u + 1})
    (F := Opens.map f₂X.base) (G := Opens.map f₁X.base)
    (FG := Opens.map (f₁X ≫ f₂X).base)
    (Opens.mapComp f₁X.base f₂X.base).symm
    (opensTopology S₀) (opensTopology S₁) (opensTopology S₂)

section DerivedZariski

variable [HasDerivedCategory.{w'} (Sheaf (opensTopology S₂) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₁) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})]

/-- **`Rf_{Zar, *}` is functorial in `f`**, `R(f₁ ≫ f₂)_{Zar, *} ≅ Rf₁_{Zar, *} ⋙ Rf₂_{Zar, *}`.
Unconditional: the underived statement is `zariskiPushforwardComp` and the comparison of
[Stacks, Tag 05T2] is invertible because `f₁_{Zar, *}` preserves injective abelian sheaves
(`preservesInjectiveObjects_zariskiPushforward`). -/
def derivedZariskiPushforwardComp :
    derivedZariskiPushforwardFunctor S₂ S₀ (f₁X ≫ f₂X) ≅
      derivedZariskiPushforwardFunctor S₂ S₁ f₁X ⋙ derivedZariskiPushforwardFunctor S₁ S₀ f₂X :=
  Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso
    (zariskiPushforward S₂ S₁ f₁X) (zariskiPushforward S₁ S₀ f₂X)
    (zariskiPushforward S₂ S₀ (f₁X ≫ f₂X)) (zariskiPushforwardComp)

end DerivedZariski

/-! ### The (TR 4) step of [Stacks, Tag 07Q9] in the shape of its own conclusion -/

section Annihilation

variable (S₀)
variable [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})]

/-- **The annihilators of [Stacks, Tag 07Q9] multiply along a composition.**  If `a` is an
annihilator of the cohomology sheaves of the cone of `α` in the sense of `Annihilation07Q9`, and
`b` one for `β`, then `a * b` is one for `α ≫ β`.

This is the (TR 4) step the source performs on the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X`, stated in the
*binary* form that an induction over `AlgebraicGeometry.IsAlphaPCoverComposite` consumes and in
terms of `Annihilation07Q9` itself, so that the per-stage statement and the composite statement
are literally the same predicate.  Unconditional: it is
`Stacks.Triangulated.mul_smul_id_homologyFunctor_eq_zero_of_comp`, the octahedron axiom followed
by the cohomology long exact sequence.

What it does *not* supply is the identification of the comparison map of a composite cover with
the composite of the comparison maps of its stages.  All three inputs to that identification
named in the module documentation are settled: `HasCrisDirectImageComp` above,
`...SmallSite.crisInverseImageComp`, and the coherence of the commutation data of the squares of
topoi, `...SmallSite.CrisZariskiCellComp` of `SmallSite/CrisZariskiSquareComposition.lean`, which
`SmallSite/CrisZariskiCellCompositionProof.lean` proves and from which that module derives the
composition functoriality of the underived comparison map. -/
theorem annihilation07Q9_comp (a b : ℕ)
    {A B₁ B₂ : DerivedCategory.Plus (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})}
    (α : A ⟶ B₁) (β : B₁ ⟶ B₂)
    (hα : Annihilation07Q9 S₀ a α) (hβ : Annihilation07Q9 S₀ b β) :
    Annihilation07Q9 S₀ (a * b) (α ≫ β) := by
  intro E v wE hT j
  have h := Stacks.Triangulated.mul_smul_id_homologyFunctor_eq_zero_of_comp α β (a : ℤ) (b : ℤ)
    (fun W v' w' hW j' ↦ hα W v' w' hW j') (fun W v' w' hW j' ↦ hβ W v' w' hW j') v wE hT j
  simpa using h

end Annihilation

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
