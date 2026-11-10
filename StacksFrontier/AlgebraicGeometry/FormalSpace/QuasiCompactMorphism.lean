module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Quasi-compact morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` is *quasi-compact* (**Stacks 0AJC**) when the fibre product
`X ×_Y T` is a quasi-compact formal algebraic space for every affine scheme `T` over `S` in
the site mapping to `Y`. **Stacks 0AJB** lists the conditions equivalent to it: the induced
morphism of reductions is a quasi-compact morphism of algebraic spaces, the same fibre
product condition over quasi-compact schemes, the same over affine schemes, and the same
along the members of some covering of `Y` as in Definition 0AIM.

A formal algebraic space over `S` is *quasi-compact* when it receives a surjective étale
morphism, representable by algebraic spaces, from an affine formal algebraic space; this is
condition (3) of Stacks 0AJ9.

For a morphism which is representable by algebraic spaces there is a second notion of
quasi-compactness, the one of Bootstrap, Definition 03XZ: the property of morphisms of
algebraic spaces over `S` tested on every base change to a scheme over `S` in the site.
**Stacks 0AM2** is the agreement of the two notions.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`: a quasi-compact formal algebraic space
  over `S`, in the form of condition (3) of Stacks 0AJ9.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions`,
  `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges`,
  `AlgebraicGeometry.FormalSpace.IsQuasiCompact`,
  `AlgebraicGeometry.FormalSpace.HasQuasiCompactFormalAtlas`: conditions (1), (2), (3) and
  (4) of **Stacks 0AJB**.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompact`: **Stacks 0AJC**, condition (3) being the
  one taken as the definition.
* `AlgebraicGeometry.FormalSpace.QuasiCompactSpaceAgreesOnAlgebraicSpaces`: agreement of
  quasi-compactness of a formal algebraic space over `S` with quasi-compactness of an
  algebraic space over `S` on those fppf sheaves which are algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.isFormalAlgebraicSpace`: a quasi-compact
  formal algebraic space over `S` is a formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact`: the
  implication (2) ⇒ (3) of **Stacks 0AJB**.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompact.of_isPullback`: a base change of a
  quasi-compact morphism is quasi-compact.
* `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnSchemeBaseChanges.of_isPullback`: the same
  for condition (2).
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_hasPropertyULift`: **Stacks 0AM2**, the
  agreement of Stacks 0AJC with Bootstrap, Definition 03XZ for a morphism representable by
  algebraic spaces.

## Implementation notes

Quasi-compactness of a formal algebraic space over `S` is read as condition (3) of
Stacks 0AJ9 — a single affine formal algebraic space mapping onto it by a morphism which is
representable by algebraic spaces, étale and surjective — together with the set-theoretic
condition of Stacks 0AIS, so that it is a condition on an arbitrary fppf sheaf and implies
being a formal algebraic space in the sense of Stacks 0AIM, which
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace.isFormalAlgebraicSpace` records. That
condition is the one of the three in Stacks 0AJ9 that needs no finiteness bookkeeping and no
reduction; the equivalence of the three is Stacks 0AJ9 itself.

Conditions (2), (3) and (4) quantify over the fibre product `X ×_Y T` as a cartesian square
rather than over the chosen `CategoryTheory.Limits.pullback`, as the conditions of
Stacks 0GHS and Stacks 0ART in this library do, so that they speak about every fibre product.
The test objects are the objects of the big fppf site of `S` with quasi-compact, respectively
affine, underlying scheme, these being the schemes over `S` the site provides. Condition (4)
is spelled out rather than abbreviated, since the covering of Stacks 0AIM is the atlas
appearing in the definition of a formal algebraic space and that definition does not name it.
None of the conditions uses the witnesses that the source and the target are formal algebraic
spaces, so all are stated for an arbitrary morphism of fppf sheaves, exactly as
`AlgebraicGeometry.FormalSpace.IsSurjective` and `AlgebraicGeometry.FormalSpace.IsProper`
are.

Condition (1) is not phrased through a chosen reduction, which would need a choice. It is
phrased instead, as Stacks 0GB8 is, with the two reductions, their inclusions and the induced
morphism quantified over: `AlgebraicGeometry.FormalSpace.IsQuasiCompactOnReductions` asks
that every morphism of reductions compatible with `f` be a quasi-compact morphism of
algebraic spaces. Reductions exist, by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`, so this is the
condition of Stacks 0AJB on `f_red`. Quasi-compactness of the morphism of reductions is the
universe-lifted notion of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType` for a
value universe independent of the universe of the schemes, since the sheaves carrying formal
algebraic spaces take values in `Type (u + 1)`.

Of the implications among the four conditions of Stacks 0AJB only (2) ⇒ (3) is formalized.
The implication (3) ⇒ (2) needs a finite covering of a quasi-compact scheme over `S` by affine
schemes inside the site and the assembly of the resulting finitely many quasi-compact fibre
products into one, which rests on the equivalence of the three conditions of Stacks 0AJ9; the
implications relating condition (1) to the others need in addition that the reduction of a
fibre product be the fibre product of the reductions, which combines Stacks 0AIN with
Stacks 0AJ9.

The two sides of Stacks 0AM2 are the fibre product condition of Stacks 0AJC over the affine
schemes of the site and the bootstrap condition of Stacks 03XZ, tested on quasi-compactness
of morphisms of algebraic spaces over `S` in the value universe `u + 1` of the formal
algebraic spaces; the latter is `AlgebraicGeometry.Space.HasPropertyULift` evaluated at
`AlgebraicGeometry.Space.quasiCompactPropertyULift`, which is the spelling of Stacks 03XZ for
a value universe independent of the universe of the schemes. The two inputs from Stacks 0AJB
are carried as the hypotheses `QuasiCompactSpaceAgreesOnAlgebraicSpaces` and the implication
(3) ⇒ (2) for the morphism at hand: the first is the equivalence of the three conditions of
Stacks 0AJ9 compared with Stacks 03E3 on a sheaf which happens to be an algebraic space, the
second the implication of Stacks 0AJB discussed above. Beyond these, a fibre product with a
scheme-valued point of the target is an algebraic space by representability, the bootstrap
condition over an affine scheme is the
fibre product condition over it because a scheme in the site is a quasi-compact algebraic
space when its underlying scheme is quasi-compact, and conversely the bootstrap condition
over an arbitrary scheme of the site follows from the fibre product condition over the
quasi-compact ones, a quasi-compact algebraic space receiving a surjective étale morphism
from a quasi-compact scheme of the site.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compact formal algebraic spaces -/

/-- **Stacks 0AJ9, condition (3).** An fppf sheaf on the big fppf site of `S` is a
*quasi-compact formal algebraic space* over `S` when it satisfies the set-theoretic condition
of Stacks 0AIS and receives a morphism from an affine formal algebraic space which is
representable by algebraic spaces, étale and a surjection of sheaves. -/
abbrev IsQuasiCompactSpace (X : FppfSheaf B S hS) : Prop :=
  SatisfiesSetTheoreticCondition B S hS X ∧
    ∃ (Z : FppfSheaf B S hS) (c : Z ⟶ X),
      IsAffineFormalAlgebraicSpace B S hS Z ∧
      (∃ hc : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) c.hom hc) ∧
      Sheaf.IsLocallySurjective c

/-- A quasi-compact formal algebraic space over `S` is a formal algebraic space over `S`: the
one affine formal algebraic space mapping onto it is an atlas as in Definition 0AIM indexed
by a one-point type, the induced map from the coproduct over that type being the given map up
to the coproduct inclusion, which is a split epimorphism. -/
theorem IsQuasiCompactSpace.isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (h : IsQuasiCompactSpace B S hS X) : IsFormalAlgebraicSpace B S hS X := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hset, Z, c, haffine, hetale, hsurjective⟩ := h
  refine ⟨hset, PUnit.{u + 2}, fun _ ↦ Z, fun _ ↦ c, fun _ ↦ haffine, fun _ ↦ hetale, ?_⟩
  have : Epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit ≫
      Sigma.desc (fun _ : PUnit.{u + 2} ↦ c)) := by
    rw [Sigma.ι_comp_desc]
    exact (Sheaf.isLocallySurjective_iff_epi c).mp hsurjective
  exact (Sheaf.isLocallySurjective_iff_epi _).mpr
    (epi_of_epi (Sigma.ι (fun _ : PUnit.{u + 2} ↦ Z) PUnit.unit) _)

/-! ### The conditions of Stacks 0AJB -/

/-- **Stacks 0AJB, condition (1).** A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf
site of `S` is *quasi-compact on reductions* when every morphism between reductions of `X` and
of `Y` compatible with `f` is a quasi-compact morphism of algebraic spaces. The reductions are
quantified over rather than chosen from Stacks 0AIN, so no choice is needed. -/
abbrev IsQuasiCompactOnReductions {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Xred Yred : FppfSheaf B S hS) (iX : Xred ⟶ X) (iY : Yred ⟶ Y),
    IsReduction B S hS X Xred iX → IsReduction B S hS Y Yred iY →
      ∀ fred : Xred ⟶ Yred, fred ≫ iY = iX ≫ f →
        Space.IsQuasiCompactULift.{u + 1} B S hS fred.hom

/-- **Stacks 0AJB, condition (2).** Every fibre product of a morphism of fppf sheaves on the
big fppf site of `S` with a quasi-compact scheme over `S` in the site mapping to its target is
a quasi-compact formal algebraic space over `S`. -/
abbrev IsQuasiCompactOnSchemeBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f →
        IsQuasiCompactSpace B S hS W

/-- **Stacks 0AJC**, in the form of **Stacks 0AJB, condition (3)**. A morphism of formal
algebraic spaces over `S` is *quasi-compact* when every fibre product of it with an affine
scheme over `S` in the site mapping to its target is a quasi-compact formal algebraic space
over `S`. The condition makes sense, and is stated, for an arbitrary morphism of fppf sheaves
on the big fppf site of `S`. -/
@[stacks 0AJC "condition (3) of Stacks 0AJB taken as the definition"]
abbrev IsQuasiCompact {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ (g : yonedaSheaf B S hS T ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X), IsPullback p q g f →
        IsQuasiCompactSpace B S hS W

/-- **Stacks 0AJB, condition (4).** There is a covering of the target of a morphism of fppf
sheaves on the big fppf site of `S` as in Definition 0AIM — by affine formal algebraic spaces,
along morphisms representable by algebraic spaces and étale, jointly surjective as a map of
sheaves — all of whose fibre products with the morphism are quasi-compact formal algebraic
spaces over `S`. -/
abbrev HasQuasiCompactFormalAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y),
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Yi i)) ∧
    (∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci) ∧
    Sheaf.IsLocallySurjective (Sigma.desc c) ∧
    ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → IsQuasiCompactSpace B S hS W

/-! ### The implication (2) implies (3) -/

/-- **Stacks 0AJB, condition (2) implies condition (3).** The fibre product condition over the
quasi-compact schemes over `S` in the site restricts to the affine ones, an affine scheme
being quasi-compact. -/
@[stacks 0AJB "condition (2) implies condition (3); no other implication among the four \
conditions is proved here"]
theorem IsQuasiCompactOnSchemeBaseChanges.isQuasiCompact {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsQuasiCompactOnSchemeBaseChanges B S hS f) : IsQuasiCompact B S hS f :=
  fun T _ => h T inferInstance

/-! ### Base change -/

/-- A base change of a quasi-compact morphism of fppf sheaves on the big fppf site of `S` is
quasi-compact: a fibre product of the base change with an affine scheme over `S` in the site
is, by pasting the two cartesian squares, a fibre product of the original morphism with that
same scheme. -/
theorem IsQuasiCompact.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsQuasiCompact B S hS f) : IsQuasiCompact B S hS p :=
  fun T hT c V a b sq' => hf T hT (c ≫ g) V a (b ≫ q) (sq'.paste_vert sq)

/-- A base change of a morphism of fppf sheaves on the big fppf site of `S` satisfying
condition (2) of Stacks 0AJB satisfies condition (2): a fibre product of the base change with
a quasi-compact scheme over `S` in the site is, by pasting the two cartesian squares, a fibre
product of the original morphism with that same scheme. -/
theorem IsQuasiCompactOnSchemeBaseChanges.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsQuasiCompactOnSchemeBaseChanges B S hS f) :
    IsQuasiCompactOnSchemeBaseChanges B S hS p :=
  fun T hT c V a b sq' => hf T hT (c ≫ g) V a (b ≫ q) (sq'.paste_vert sq)

/-! ### Comparison with the bootstrap notion of Stacks 03XZ -/

/-- Agreement of the two notions of quasi-compactness of an fppf sheaf on the big fppf site of
`S` on those sheaves which are algebraic spaces over `S`: such a sheaf is a quasi-compact
formal algebraic space, in the form of condition (3) of Stacks 0AJ9 taken here as
`AlgebraicGeometry.FormalSpace.IsQuasiCompactSpace`, exactly when it is a quasi-compact
algebraic space in the sense of Stacks 03E3.

One implication produces a quasi-compact scheme chart out of an affine formal algebraic space
chart, the other an affine formal algebraic space chart out of a quasi-compact scheme chart;
both are instances of the equivalence of the three conditions of Stacks 0AJ9 and of the
comparison of that equivalence with Stacks 03E3. -/
abbrev QuasiCompactSpaceAgreesOnAlgebraicSpaces : Prop :=
  ∀ W : FppfSheaf B S hS, Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj →
    (IsQuasiCompactSpace B S hS W ↔ Space.IsQuasiCompactSpaceULift.{u + 1} B S hS W.obj)

/-- Étaleness of the morphism of schemes underlying a morphism of the big fppf site of `S`,
read as a property of morphisms of the site. -/
public abbrev etaleProperty : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

/-- A property of morphisms of the big fppf site of `S` which holds for isomorphisms holds
after every represented base change of the identity of a universe-lifted Yoneda presheaf. -/
private theorem relative_id_of_isomorphisms (Q : MorphismProperty (BigFppfOver B S hS))
    (hQ : ∀ ⦃V W : BigFppfOver B S hS⦄ (φ : V ⟶ W), IsIso φ → Q φ)
    (T : BigFppfOver B S hS) :
    Q.relative (uliftYoneda.{u + 1}) (𝟙 ((uliftYoneda.{u + 1}).obj T)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  exact hQ snd ‹IsIso snd›

/-- The identity of a universe-lifted Yoneda presheaf is étale after every represented base
change. -/
private theorem relative_id_etale (T : BigFppfOver B S hS) :
    (etaleProperty B S hS).relative (uliftYoneda.{u + 1})
      (𝟙 ((uliftYoneda.{u + 1}).obj T)) := by
  refine relative_id_of_isomorphisms B S hS _ (fun _ _ φ hφ => ?_) T
  have := hφ
  change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ)
  infer_instance


/-- Étaleness of the morphism of schemes underlying a morphism of the big fppf site of `S` is
stable under composition. -/
@[sga "1 I 4.6" "(ii), special case"]
private instance etaleProperty_isStableUnderComposition :
    (etaleProperty B S hS).IsStableUnderComposition :=
  have : MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- A relative morphism property along the universe-lifted Yoneda embedding is stable under
base change. -/
private theorem relative_of_isPullback {Q : MorphismProperty (BigFppfOver B S hS)}
    {F G K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {p : L ⟶ F} {q : L ⟶ G}
    {m : F ⟶ K} {n : G ⟶ K} (sq : IsPullback p q m n)
    (hn : Q.relative (uliftYoneda.{u + 1}) n) : Q.relative (uliftYoneda.{u + 1}) p :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{u + 1})
    Q).of_isPullback sq.flip hn


/-- A scheme over `S` in the site with quasi-compact underlying scheme is a quasi-compact
algebraic space over `S`, the identity serving as its chart. -/
private theorem isQuasiCompactSpaceULift_uliftYoneda (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj T) :=
  ⟨T, 𝟙 _, hT, Space.relative_id_surjective B S hS T, fun _ φ hφ => by simpa using hφ⟩

/-- A morphism of presheaves on the big fppf site of `S` with values in `Type (u + 1)` is
quasi-compact in the sense of Stacks 03HE as soon as its fibre product with every
scheme-valued point of its target whose underlying scheme is quasi-compact is a quasi-compact
algebraic space over `S`. A quasi-compact algebraic space mapping to the target receives a
surjective étale morphism from a quasi-compact scheme in the site, and the fibre product along
the resulting scheme-valued point is a quasi-compact surjective étale chart of the fibre
product along the given morphism. -/
private theorem isQuasiCompactULift_of_forall_compact
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (p : F ⟶ G)
    (h : ∀ (V : BigFppfOver B S hS), CompactSpace ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ η : (uliftYoneda.{u + 1}).obj V ⟶ G,
        Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback η p)) :
    Space.IsQuasiCompactULift.{u + 1} B S hS p := by
  intro Z _ hZqc g
  obtain ⟨V, c, hVc, hcSurj, hcEtale⟩ := hZqc
  have hcE := (Space.isEtaleULift_iff_relative_etale B S hS c).mp hcEtale
  let k : pullback (c ≫ g) p ⟶ pullback g p :=
    pullback.lift (pullback.fst (c ≫ g) p ≫ c) (pullback.snd (c ≫ g) p)
      (by rw [Category.assoc]; exact pullback.condition)
  have hbig : IsPullback (pullback.fst (c ≫ g) p) (k ≫ pullback.snd g p) (c ≫ g) p := by
    simpa only [k, pullback.lift_snd] using IsPullback.of_hasPullback (c ≫ g) p
  have hsquare : IsPullback k (pullback.fst (c ≫ g) p) (pullback.fst g p) c :=
    (hbig.of_bot (by dsimp only [k]; rw [pullback.lift_fst])
      (IsPullback.of_hasPullback g p)).flip
  obtain ⟨W, γ, hWc, hγSurj, hγEtale⟩ := h V hVc (c ≫ g)
  exact ⟨W, γ ≫ k, hWc,
    Space.relative_comp B S hS hγSurj (Space.relative_of_isPullback B S hS hsquare hcSurj),
    (Space.isEtaleULift_iff_relative_etale B S hS (γ ≫ k)).mpr
      (Space.relative_comp B S hS ((Space.isEtaleULift_iff_relative_etale B S hS γ).mp hγEtale)
        (Space.relative_of_isPullback B S hS hsquare hcE))⟩

/-- For a morphism of fppf sheaves on the big fppf site of `S` which is representable by
algebraic spaces, a fibre product of it with a scheme-valued point of its target is a
quasi-compact formal algebraic space over `S` exactly when the fibre product of the underlying
presheaves is a quasi-compact algebraic space over `S`: the fibre product is an algebraic
space by representability, and the two notions agree there. -/
private theorem isQuasiCompactSpace_iff_isQuasiCompactSpaceULift
    (hagree : QuasiCompactSpaceAgreesOnAlgebraicSpaces B S hS) {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {T : BigFppfOver B S hS} {g : yonedaSheaf B S hS T ⟶ Y} {W : FppfSheaf B S hS}
    {p : W ⟶ yonedaSheaf B S hS T} {q : W ⟶ X} (sq : IsPullback p q g f) :
    IsQuasiCompactSpace B S hS W ↔
      Space.IsQuasiCompactSpaceULift.{u + 1} B S hS (pullback g.hom f.hom) := by
  have hsq : IsPullback p.hom q.hom g.hom f.hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  refine (hagree W (Space.isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback.symm
    (hf T g.hom))).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Space.isQuasiCompactSpaceULift_of_iso B S hS hsq.isoPullback h
  · exact Space.isQuasiCompactSpaceULift_of_iso B S hS hsq.isoPullback.symm h

/-- **Stacks 0AM2.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which
is representable by algebraic spaces. Then `f` is quasi-compact in the sense of Stacks 0AJC —
every fibre product of it with an affine scheme over `S` in the site is a quasi-compact formal
algebraic space — exactly when it is quasi-compact in the sense of Bootstrap, Definition
03XZ: every fibre product of it with a scheme over `S` in the site is quasi-compact over that
scheme as a morphism of algebraic spaces.

Both directions pass through the agreement of the two notions of quasi-compactness of a space
on an algebraic space, which is the hypothesis
`AlgebraicGeometry.FormalSpace.QuasiCompactSpaceAgreesOnAlgebraicSpaces`. For the remaining
direction the bootstrap condition must be tested against the quasi-compact, not only the
affine, schemes over `S` in the site, which is the implication (3) ⇒ (2) of Stacks 0AJB and is
the second hypothesis. The witnesses that the source and the target are formal algebraic
spaces are not used, so the statement is for an arbitrary morphism of fppf sheaves. -/
@[stacks 0AM2 "both directions, for an arbitrary morphism of fppf sheaves representable by \
algebraic spaces, with two named hypotheses: `QuasiCompactSpaceAgreesOnAlgebraicSpaces`, the \
agreement of the quasi-compactness notions of Stacks 0AJ9 and Stacks 03E3 on an algebraic \
space, and the implication (3) ⇒ (2) of Stacks 0AJB for the morphism"]
theorem isQuasiCompact_iff_hasPropertyULift {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hagree : QuasiCompactSpaceAgreesOnAlgebraicSpaces B S hS)
    (hbase : IsQuasiCompact B S hS f → IsQuasiCompactOnSchemeBaseChanges B S hS f) :
    IsQuasiCompact B S hS f ↔
      Space.HasPropertyULift.{u + 1} B S hS
        (Space.quasiCompactPropertyULift.{u + 1} B S hS) f.hom hf := by
  refine ⟨fun hqc U ξ => ?_, fun h T _ g W p q sq => ?_⟩
  · change Space.IsQuasiCompactULift.{u + 1} B S hS (pullback.fst ξ f.hom)
    refine isQuasiCompactULift_of_forall_compact B S hS _ (fun V hV η => ?_)
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS
      (pullbackRightPullbackFstIso ξ f.hom η).symm ?_
    exact (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift B S hS hagree hf
      (IsPullback.of_hasPullback (⟨η ≫ ξ⟩ : yonedaSheaf B S hS V ⟶ Y) f)).mp
      (hbase hqc V hV _ _ _ _ (IsPullback.of_hasPullback _ f))
  · refine (isQuasiCompactSpace_iff_isQuasiCompactSpaceULift B S hS hagree hf sq).mpr ?_
    refine Space.isQuasiCompactSpaceULift_of_iso B S hS
      (IsPullback.of_id_snd (f := pullback.fst g.hom f.hom)).isoPullback.symm ?_
    exact h T g.hom _ (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T)
      (isQuasiCompactSpaceULift_uliftYoneda B S hS T inferInstance) (𝟙 _)

end AlgebraicGeometry.FormalSpace

end
