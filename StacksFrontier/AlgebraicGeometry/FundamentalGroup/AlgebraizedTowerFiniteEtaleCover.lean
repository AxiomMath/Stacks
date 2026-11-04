module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleNeighbourhoodOfClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleThickeningTower
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NeighborhoodCompletionInput

/-!
# From an algebraized tower to a finite étale cover of a neighbourhood

Let `X` be a locally Noetherian scheme, let `Y ⊆ X` be the closed subscheme cut out by an ideal
sheaf, and let `A` be a finite étale cover of `Y`. The essential-image clause of
[Stacks, Tag 0EK1] asks for an open neighbourhood `V` of `Y` in `X` and a finite étale cover of
`V` restricting to `A`. The source produces it in five steps:

1. lift `A` to a tower of finite étale covers `π_n : U_n ⟶ Y_n` over the infinitesimal
   neighbourhoods of `Y`, by [Stacks, Tag 0BQB]
   (`AlgebraicGeometry.finiteEtaleTowerOfInfinitesimalNeighbourhoods`);
2. algebraize the finite locally free object `(π_{n, *}𝒪_{U_n})` of `Coh(X, I)` to a coherent
   module on a neighbourhood, by the essential-surjectivity half of [Stacks, Tag 0EL7];
3. transport the multiplications and units of the tower to the algebraized module, shrinking the
   neighbourhood twice;
4. take the relative spectrum, which is finite locally free over the neighbourhood
   (`Stacks.FundamentalGroup.moduleAlgebraSpecToBase`);
5. shrink once more to an open over which it is étale, by part (2) of [Stacks, Tag 0A43].

Steps 1–4 produce one piece of data — a finite morphism, locally of finite presentation, over an
open neighbourhood of `Y`, whose base change to every infinitesimal neighbourhood of `Y` is
étale and whose base change to `Y` itself is `A`. That is what
`Stacks.FundamentalGroup.AlgebraizedTowerCover` packages, and **this file proves that such a
datum already yields the essential-image clause**: step 5, together with the bookkeeping that
turns the open produced there into a neighbourhood of the chapter and the finite étale morphism
over it into an object of `FÉt` whose restriction to `Y` is `A`.

Nothing about ampleness, properness or depth is used. The depth hypothesis of
[Stacks, Tag 0ELD] enters only in the production of the datum, which is where the whole
mathematical content of steps 2 and 3 sits, and that production is **not** carried out here; it
is named `Stacks.FundamentalGroup.TowerAlgebraizationFromDepth` and remains a hypothesis.

## Main definitions

* `Stacks.FundamentalGroup.AlgebraizedTowerCover` — the output of steps 1–4 of the construction
  above, as data: a neighbourhood `V` of the closed subscheme, a finite morphism of finite
  presentation `π : U ⟶ V`, the étaleness of its base change to every infinitesimal
  neighbourhood of `Y`, and a square exhibiting the given cover `A` as the base change of `π`
  along `Y ⟶ V`.
* `Stacks.FundamentalGroup.TowerAlgebraizationFromDepth` — the production of that datum under the
  hypotheses of [Stacks, Tag 0ELD], as a statement about general objects. This is the residual
  carry: it is the essential-surjectivity half of [Stacks, Tag 0EL7] composed with steps 1, 3
  and 4 of the construction in the proof of [Stacks, Tag 0EK1].

## Main results

* `Stacks.FundamentalGroup.exists_finiteEtale_neighborhood_of_algebraizedTowerCover` — the
  essential-image clause of [Stacks, Tag 0EK1] from an `AlgebraizedTowerCover`. This is step 5
  and the bookkeeping around it, and it is proved unconditionally.
* `Stacks.FundamentalGroup.finiteEtaleAlgebraizationFromDepth_of_towerAlgebraization` —
  `Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth`, the essential-surjectivity half
  of [Stacks, Tag 0ELD] as a statement about general objects, follows from
  `Stacks.FundamentalGroup.TowerAlgebraizationFromDepth`.
* `Stacks.FundamentalGroup.towerAlgebraizationFromDepth_of_finiteEtaleAlgebraization` — the
  converse, so that the change of carry is seen to smuggle nothing in. See the vacuity check
  below.
* `Stacks.FundamentalGroup.etale_pullback_of_finiteEtale_iso` — the étaleness hypothesis of
  `AlgebraizedTowerCover` is discharged by an identification of the base change at stage `n`
  with a finite étale cover of `Y_n`, which is how step 1 feeds it: the tower
  `AlgebraicGeometry.finiteEtaleTowerOfInfinitesimalNeighbourhoods` supplies those covers.

## What is and is not proved here

**No `stacks` attribute is attached to anything in this file.** The essential-image clause of
[Stacks, Tag 0EK1] is a statement at the source's hypothesis — the completion functor out of the
*colimit* being an equivalence on finite locally free objects — and that hypothesis is not what
is assumed here; what is assumed is the datum it produces. The clause is also not
[Stacks, Tag 0ELD]: Tag 0ELD is the equivalence, whose full-faithfulness half is proved
elsewhere.

The residual is exactly `TowerAlgebraizationFromDepth` and nothing else. What it carries is
steps 1–4: the lift of the tower, the algebraization of `(π_{n, *}𝒪_{U_n})` by
[Stacks, Tag 0EL7], the transport of the algebra structure, and the relative spectrum. Of those,
the lift is available (`AlgebraicGeometry.finiteEtaleTowerOfInfinitesimalNeighbourhoods`), as is
the relative spectrum, with its finiteness and finite presentation
(`Stacks.FundamentalGroup.isFinite_moduleAlgebraSpecToBase`,
`Stacks.FundamentalGroup.locallyOfFinitePresentation_moduleAlgebraSpecToBase`). The two with no
carrier are the algebraization — [Stacks, Tag 0EL7] as formalized gives a coherent module on an
**object-dependent** neighbourhood, and the finite locally free objects of `Coh(X, I)` that it
consumes have no constructor from a tower of finite étale covers in this library — and the
transport of the multiplication, whose shrinking form is the undischarged `hmul` of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsShrinkingBridge`.

## Vacuity: the residual carry is inter-derivable with the one it replaces

This is checked in both directions, machine-checked, and reported rather than hidden.

* **Residual `⟹` carry.** `finiteEtaleAlgebraizationFromDepth_of_towerAlgebraization`, which is
  the point of the file.
* **Carry `⟹` residual.** `towerAlgebraizationFromDepth_of_finiteEtaleAlgebraization`, through
  `Stacks.FundamentalGroup.nonempty_algebraizedTowerCover_of_finiteEtale_neighborhood`: a finite
  étale cover of a neighbourhood *is* an `AlgebraizedTowerCover`, because a finite étale morphism
  is finite and locally of finite presentation and étaleness is stable under base change.

So `TowerAlgebraizationFromDepth` is **not** weaker than
`FiniteEtaleAlgebraizationFromDepth`; the two are equivalent, as any two carriers of one
existential conclusion in the same vocabulary must be. The honest summary is therefore: the
essential-surjectivity half of [Stacks, Tag 0ELD] is **not** discharged here. What is delivered
is (i) the proved implication, which puts the last step of the source's construction — the
shrinking of [Stacks, Tag 0A43], the passage to an object of `FÉt`, the identification of an open
of a neighbourhood with a smaller neighbourhood of the chapter, and the comparison of the two
base changes — into the library instead of leaving it to whoever discharges the carry, and
(ii) the restatement of the carry at the interface steps 1–4 actually produce, which is a finite
morphism of finite presentation and not an object of `FÉt`, so that the eventual discharge need
not reprove step 5.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-! ### Étaleness of the base changes, from the tower -/

/-- **Étaleness is transported along an isomorphism over the base.** -/
public theorem etale_of_iso_over {S P Q : Scheme.{u}} {p : P ⟶ S} {q : Q ⟶ S} (e : P ≅ Q)
    (he : e.hom ≫ q = p) (hq : Etale q) : Etale p := by
  rw [← he]
  infer_instance

/-- **The étaleness hypothesis of `Stacks.FundamentalGroup.AlgebraizedTowerCover`, from the tower
of finite étale covers.** If the base change of `π : U ⟶ V` to the `n`-th infinitesimal
neighbourhood of a closed subscheme is isomorphic, over that neighbourhood, to a finite étale
cover of it, then that base change is étale. Step 1 of the construction supplies the covers, as
`AlgebraicGeometry.finiteEtaleTowerOfInfinitesimalNeighbourhoods`. -/
public theorem etale_pullback_of_finiteEtale_iso {V Z U : Scheme.{u}} (c : Z ⟶ V)
    [IsClosedImmersion c] (f : U ⟶ V) (n : ℕ)
    (B : AlgebraicGeometry.FiniteEtaleOver
      (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood c n))
    (e : pullback f (Stacks.Thickenings.nthOrderToBase c n) ≅ B.left)
    (he : e.hom ≫ B.hom = pullback.snd f (Stacks.Thickenings.nthOrderToBase c n)) :
    Etale (pullback.snd f (Stacks.Thickenings.nthOrderToBase c n)) :=
  etale_of_iso_over e he B.prop.2

/-! ### The datum produced by steps 1–4 of the construction -/

/-- **The output of the first four steps of the construction in the proof of
[Stacks, Tag 0EK1]**, for a finite étale cover `A` of the closed subscheme cut out by `Y`: an
open neighbourhood of that subscheme, a finite morphism of finite presentation onto it whose base
change to every infinitesimal neighbourhood of the subscheme is étale, and a square exhibiting
`A` as its base change to the subscheme.

In the source the morphism is the relative spectrum of the algebraization of the tower
`(π_{n, *}𝒪_{U_n})` of a tower of finite étale covers of the infinitesimal neighbourhoods, with
the multiplication transported from the tower; the étaleness of the base changes comes from the
isomorphism of that base change with the tower stage `U_n ⟶ Y_n`
(`Stacks.FundamentalGroup.etale_pullback_of_finiteEtale_iso`). None of that is part of the
datum: only its four consequences are, which is what the remaining step of the construction
uses. -/
public structure AlgebraizedTowerCover {X : Scheme.{u}} (Y : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver Y.subscheme) where
  /-- The open neighbourhood of the closed subscheme over which the cover lives. -/
  nbhd : Neighborhood X Y
  /-- The scheme covering that neighbourhood. -/
  cover : Scheme.{u}
  /-- Its structure morphism to the neighbourhood. -/
  toBase : cover ⟶ (Neighborhood.open X Y nbhd).toScheme
  /-- The structure morphism is finite. -/
  isFinite_toBase : IsFinite toBase
  /-- The structure morphism is locally of finite presentation. -/
  locallyOfFinitePresentation_toBase : LocallyOfFinitePresentation toBase
  /-- Its base change to every infinitesimal neighbourhood of the closed subscheme is étale. -/
  etale_pullback_nthOrder : ∀ n : ℕ, Etale (pullback.snd toBase
    (Stacks.Thickenings.nthOrderToBase (Neighborhood.toSchemeHom X Y nbhd) n))
  /-- The morphism from the given cover of the closed subscheme to the covering scheme. -/
  restrictHom : A.left ⟶ cover
  /-- The given cover of the closed subscheme is the base change of the covering scheme. -/
  isPullback_restrictHom : IsPullback restrictHom A.hom toBase
    (Neighborhood.toSchemeHom X Y nbhd)

/-! ### The last step: shrinking to a finite étale cover of a smaller neighbourhood -/

section

variable {X : Scheme.{u}} {Y : X.IdealSheafData}

/-- A generalized point of a base-changed finite étale cover, given by its two components. As in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction`, the `pullback.lift` is
wrapped in a definition stated at the type of the base-changed object: written out it is not
type-correct at reducible transparency. -/
private def towerCoverLift {S T : Scheme.{u}} (u : S ⟶ T)
    (B : AlgebraicGeometry.FiniteEtaleOver T) {Z : Scheme.{u}} (p : Z ⟶ B.left) (z : Z ⟶ S)
    (hp : p ≫ B.hom = z ≫ u) :
    Z ⟶ ((AlgebraicGeometry.finiteEtaleBaseChange u).obj B).left :=
  pullback.lift p z hp

private theorem towerCoverLift_comp_proj {S T : Scheme.{u}} (u : S ⟶ T)
    (B : AlgebraicGeometry.FiniteEtaleOver T) {Z : Scheme.{u}} (p : Z ⟶ B.left) (z : Z ⟶ S)
    (hp : p ≫ B.hom = z ≫ u) :
    towerCoverLift u B p z hp ≫ AlgebraicGeometry.finiteEtaleBaseChangeProj u B = p :=
  pullback.lift_fst _ _ _

private theorem towerCoverLift_comp_hom {S T : Scheme.{u}} (u : S ⟶ T)
    (B : AlgebraicGeometry.FiniteEtaleOver T) {Z : Scheme.{u}} (p : Z ⟶ B.left) (z : Z ⟶ S)
    (hp : p ≫ B.hom = z ≫ u) :
    towerCoverLift u B p z hp ≫
        ((AlgebraicGeometry.finiteEtaleBaseChange u).obj B).hom = z :=
  pullback.lift_snd _ _ _

/-- **A finite étale cover carrying a pullback square over a base change is that base change.**
If `C ⟶ S` sits in a pullback square over `E ⟶ T` along `u : S ⟶ T`, then it is isomorphic to
the image of `E` under the base-change functor. -/
private def baseChangeIsoOfIsPullback {T S : Scheme.{u}} (u : S ⟶ T)
    (E : AlgebraicGeometry.FiniteEtaleOver T) (C : AlgebraicGeometry.FiniteEtaleOver S)
    (p : C.left ⟶ E.left) (hp : IsPullback p C.hom E.hom u) :
    (AlgebraicGeometry.finiteEtaleBaseChange u).obj E ≅ C := by
  refine MorphismProperty.Over.isoMk (B := C) ⟨hp.lift
      (AlgebraicGeometry.finiteEtaleBaseChangeProj u E)
      ((AlgebraicGeometry.finiteEtaleBaseChange u).obj E).hom
      (AlgebraicGeometry.finiteEtaleBaseChangeProj_comp_hom u E),
    towerCoverLift u E p C.hom hp.w, ?_, ?_⟩ ?_
  · refine AlgebraicGeometry.finiteEtaleBaseChangeProj_hom_ext u E ?_ ?_ <;>
      simp [towerCoverLift_comp_proj, towerCoverLift_comp_hom]
  · refine hp.hom_ext ?_ ?_ <;> simp [towerCoverLift_comp_proj, towerCoverLift_comp_hom]
  · exact hp.lift_snd _ _ _

/-- **The essential-image clause of [Stacks, Tag 0EK1] from an algebraized tower.** Let `X` be a
locally Noetherian scheme, `Y ⊆ X` the closed subscheme cut out by an ideal sheaf, and `A` a
finite étale cover of `Y`. Given the datum of
`Stacks.FundamentalGroup.AlgebraizedTowerCover` — a finite morphism of finite presentation
`π : U ⟶ V` over an open neighbourhood `V` of `Y`, étale over every infinitesimal neighbourhood
of `Y`, with `A` as its base change to `Y` — there is an open neighbourhood `W` of `Y` and a
finite étale cover of `W` whose restriction to `Y` is isomorphic to `A`.

This is the last step of the source's construction. Part (2) of [Stacks, Tag 0A43] makes `π`
étale at every point above `Y`, the étale locus is open and `π` is closed, so `π` is finite étale
over an open `W₀ ⊆ V` containing `Y`
(`AlgebraicGeometry.exists_isOpen_finiteEtale_of_etale_infinitesimalNeighbourhoods`). That open
is a smaller neighbourhood of the chapter, `Stacks.FundamentalGroup.Neighborhood.shrink`, and the
restriction `π ∣_ W₀` is the cover wanted: its base change along the chapter's factorisation
`Y ⟶ W₀` is a pullback of `π` along `Y ⟶ V`, because `Y ⟶ W₀ ⟶ V` is that factorisation and the
defining square of `π ∣_ W₀` is a pullback square. -/
public theorem exists_finiteEtale_neighborhood_of_algebraizedTowerCover [IsLocallyNoetherian X]
    {A : AlgebraicGeometry.FiniteEtaleOver Y.subscheme} (D : AlgebraizedTowerCover Y A) :
    ∃ (W : Neighborhood X Y)
      (U : AlgebraicGeometry.FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((AlgebraicGeometry.finiteEtaleBaseChange
        (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) := by
  have := D.isFinite_toBase
  have := D.locallyOfFinitePresentation_toBase
  have : IsLocallyNoetherian (Neighborhood.open X Y D.nbhd).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Neighborhood.open X Y D.nbhd).ι
  obtain ⟨W₀, hW₀, hfe⟩ :=
    AlgebraicGeometry.exists_isOpen_finiteEtale_of_etale_infinitesimalNeighbourhoods
      D.toBase (Neighborhood.toSchemeHom X Y D.nbhd) D.etale_pullback_nthOrder
  have hsupp : (Stacks.Algebraization.nbhdTower Y.subschemeι
      (Neighborhood.open X Y D.nbhd)
      (Neighborhood.range_subschemeι_subset X Y D.nbhd)).support ⊆ (W₀ : Set _) := by
    rwa [nbhdTower_support_eq]
  -- The cover of `W₀`, and the factorisation of the closed subscheme through `W₀`.
  let F : AlgebraicGeometry.FiniteEtaleOver W₀.toScheme :=
    MorphismProperty.Over.mk ⊤ (D.toBase ∣_ W₀) hfe
  let g : Y.subscheme ⟶ W₀.toScheme := Neighborhood.toOpenHom X Y D.nbhd W₀ hsupp
  -- The defining square of the restriction, flipped.
  have ht : IsPullback (D.toBase ⁻¹ᵁ W₀).ι (D.toBase ∣_ W₀) D.toBase W₀.ι :=
    (AlgebraicGeometry.isPullback_morphismRestrict D.toBase W₀).flip
  have hcomm : D.restrictHom ≫ D.toBase = (A.hom ≫ g) ≫ W₀.ι := by
    rw [Category.assoc, Neighborhood.toOpenHom_ι]
    exact D.isPullback_restrictHom.w
  let k : A.left ⟶ (D.toBase ⁻¹ᵁ W₀).toScheme := ht.lift D.restrictHom (A.hom ≫ g) hcomm
  have hk₁ : k ≫ (D.toBase ⁻¹ᵁ W₀).ι = D.restrictHom := ht.lift_fst _ _ _
  have hk₂ : k ≫ (D.toBase ∣_ W₀) = A.hom ≫ g := ht.lift_snd _ _ _
  have hk : IsPullback k A.hom (D.toBase ∣_ W₀) g := by
    refine IsPullback.of_right ?_ hk₂ ht
    rw [hk₁, Neighborhood.toOpenHom_ι]
    exact D.isPullback_restrictHom
  -- `W₀` is a smaller neighbourhood of the chapter, and `g` factors through it.
  refine ⟨Neighborhood.shrink X Y D.nbhd W₀ hsupp,
    (AlgebraicGeometry.finiteEtaleBaseChange
      (Neighborhood.imageOpenIso X Y D.nbhd W₀).inv).obj F, ⟨?_⟩⟩
  exact ((AlgebraicGeometry.finiteEtaleBaseChangeComp
    (Neighborhood.toSchemeHom X Y (Neighborhood.shrink X Y D.nbhd W₀ hsupp))
    (Neighborhood.imageOpenIso X Y D.nbhd W₀).inv g rfl).app F).symm ≪≫
    baseChangeIsoOfIsPullback g F A k hk

/-- The isomorphism of underlying schemes of an isomorphism of finite étale covers. -/
private def towerCoverLeftIso {S : Scheme.{u}}
    {E C : AlgebraicGeometry.FiniteEtaleOver S} (e : E ≅ C) : E.left ≅ C.left :=
  (MorphismProperty.Comma.forget _ _ _ _ _ ⋙ Comma.fst _ _).mapIso e

/-- **The converse of
`Stacks.FundamentalGroup.exists_finiteEtale_neighborhood_of_algebraizedTowerCover`:** a finite
étale cover of a neighbourhood restricting to `A` is itself an
`Stacks.FundamentalGroup.AlgebraizedTowerCover` for `A`. A finite étale morphism is finite and
locally of finite presentation, and étaleness is stable under base change, so the only thing to
produce is the pullback square, which is the defining square of the base change transported along
the given isomorphism.

So the datum is **not** strictly stronger than the conclusion it is used to reach: the two are
inter-derivable, and `Stacks.FundamentalGroup.TowerAlgebraizationFromDepth` is equivalent to
`Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth` rather than weaker than it. What the
file delivers is the proved direction and the change of vocabulary; see the module
documentation. -/
public theorem nonempty_algebraizedTowerCover_of_finiteEtale_neighborhood
    {A : AlgebraicGeometry.FiniteEtaleOver Y.subscheme} (W : Neighborhood X Y)
    (U : AlgebraicGeometry.FiniteEtaleOver (Neighborhood.open X Y W).toScheme)
    (e : (AlgebraicGeometry.finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) :
    Nonempty (AlgebraizedTowerCover Y A) := by
  have := U.prop.1
  have := U.prop.2
  have hw : (towerCoverLeftIso e).inv ≫
      ((AlgebraicGeometry.finiteEtaleBaseChange
        (Neighborhood.toSchemeHom X Y W)).obj U).hom = A.hom :=
    MorphismProperty.Over.w e.inv
  exact ⟨{ nbhd := W
           cover := U.left
           toBase := U.hom
           isFinite_toBase := inferInstance
           locallyOfFinitePresentation_toBase := inferInstance
           etale_pullback_nthOrder := fun _ => inferInstance
           restrictHom := (towerCoverLeftIso e).inv ≫
             AlgebraicGeometry.finiteEtaleBaseChangeProj (Neighborhood.toSchemeHom X Y W) U
           isPullback_restrictHom := IsPullback.of_iso_pullback
             ⟨by rw [Category.assoc,
                 AlgebraicGeometry.finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc, hw]⟩
             (towerCoverLeftIso e).symm rfl hw }⟩

end

/-! ### The residual carry, and Tag 0ELD's essential image -/

/-- **The production of an algebraized tower cover under the hypotheses of
[Stacks, Tag 0ELD]**, as a statement about general objects: for `X` proper over a field `k`, `L`
an ample invertible `𝒪_X`-module, `s ∈ Γ(X, L)`, `Y = Z(s)` its zero scheme, and
`depth(𝒪_{X, x}) + dim({x}‾) > 2` at every `x ∈ X ∖ Y`, every finite étale cover of `Y` admits a
`Stacks.FundamentalGroup.AlgebraizedTowerCover`.

This is the residual carry of this file. It is steps 1–4 of the construction in the proof of
[Stacks, Tag 0EK1]: lift the cover to the infinitesimal neighbourhoods by [Stacks, Tag 0BQB],
push the structure sheaves forward to a finite locally free object of `Coh(X, I)`, algebraize it
by the essential-surjectivity half of [Stacks, Tag 0EL7], transport the multiplication and unit
after shrinking, and take the relative spectrum. See the module documentation for which of the
four already have carriers in this library and which two do not. -/
public def TowerAlgebraizationFromDepth : Prop :=
  ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L],
    AlgebraicGeometry.Scheme.Modules.IsAmple X L →
    ∀ s : Γ(L, ⊤), DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s) →
    ∀ A : AlgebraicGeometry.FiniteEtaleOver (zeroScheme X L s).subscheme,
      Nonempty (AlgebraizedTowerCover (zeroScheme X L s) A)

/-- **The carried essential-surjectivity hypothesis of [Stacks, Tag 0ELD] follows from
`Stacks.FundamentalGroup.TowerAlgebraizationFromDepth`.**
`Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth` is the essential-surjectivity half
of [Stacks, Tag 0ELD] as a statement about general objects, and this theorem derives it from
the earlier carry: everything the source does after taking the relative spectrum of the
algebraized tower — the shrinking of [Stacks, Tag 0A43], the passage to an object of `FÉt`, and
the comparison of the two base changes — is proved, by
`Stacks.FundamentalGroup.exists_finiteEtale_neighborhood_of_algebraizedTowerCover`.

`X` is Noetherian by `Stacks.FundamentalGroup.isNoetherian_of_isProper_of_isAmple`, which is
where properness over `k` and ampleness are used; the depth hypothesis is used only through
`TowerAlgebraizationFromDepth`. -/
public theorem finiteEtaleAlgebraizationFromDepth_of_towerAlgebraization
    (h : TowerAlgebraizationFromDepth.{u}) : FiniteEtaleAlgebraizationFromDepth.{u} := by
  intro k _ X g _ L _ hL s hdepth A
  obtain ⟨D⟩ := h k g L hL s hdepth A
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAmple k g L hL
  exact exists_finiteEtale_neighborhood_of_algebraizedTowerCover D

/-- **The converse: the residual carry follows from the carry it replaces.** Together with
`Stacks.FundamentalGroup.finiteEtaleAlgebraizationFromDepth_of_towerAlgebraization` this says
that `Stacks.FundamentalGroup.TowerAlgebraizationFromDepth` and
`Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth` are inter-derivable, so neither is
weaker than the other and nothing has been smuggled in by the change of carry. It is recorded
rather than hidden: what the file contributes is the *proved* direction — the shrinking of
[Stacks, Tag 0A43] and the neighbourhood bookkeeping — and the restatement of the carry in the
vocabulary that steps 1–4 of the source's construction hand over. -/
public theorem towerAlgebraizationFromDepth_of_finiteEtaleAlgebraization
    (h : FiniteEtaleAlgebraizationFromDepth.{u}) : TowerAlgebraizationFromDepth.{u} := by
  intro k _ X g _ L _ hL s hdepth A
  obtain ⟨W, U, ⟨e⟩⟩ := h k g L hL s hdepth A
  exact nonempty_algebraizedTowerCover_of_finiteEtale_neighborhood W U e

end Stacks.FundamentalGroup

end
