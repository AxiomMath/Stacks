module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism

/-!
# Sections of a 1-morphism of algebraic stacks (Stacks 050J)

A **section** of a 1-morphism `f : 𝒳 ⟶ 𝒯` of algebraic stacks over `S` is a 1-morphism
`s : 𝒯 ⟶ 𝒳` together with a 2-isomorphism `s ≫ f ≅ 𝟙 𝒯`. **Stacks 050J** asserts that such an
`s` is representable by algebraic spaces and locally of finite type, and that it inherits
stronger properties from `f`. All five parts are proved here: `s` is representable by algebraic
spaces and locally of finite type, it is unramified in the relative sense of Stacks 03YK as soon
as `f` is Deligne–Mumford, and in the sense of Properties of Stacks, Section 04XB it is locally
quasi-finite as soon as `f` is quasi-DM, proper as soon as `f` is separated, and quasi-compact
and quasi-separated as soon as `f` is quasi-separated.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.identityFstGraphFunctor`: the functor out of the second
  factor into a 2-fibre product whose *first* leg is an identity, and
  `CategoryTheory.TwoFibreProductOver.identityFstGraphEquivalence`: it is a quasi-inverse of the
  second projection.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_section` and
  `AlgebraicGeometry.Stack.isLocallyOfFiniteType_section`: **Stacks 050J**, the two halves of
  part (1).
* `AlgebraicGeometry.Stack.isUnramified_section`: **Stacks 050J**, part (2).
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_section`: **Stacks 050J**, part (3).
* `AlgebraicGeometry.Stack.isRelativelyProper_section`: **Stacks 050J**, part (4).
* `AlgebraicGeometry.Stack.isQuasiCompact_section` and
  `AlgebraicGeometry.Stack.isQuasiSeparated_section`: **Stacks 050J**, the two halves of
  part (5).
* `AlgebraicGeometry.Stack.relativeProperty_section_of_graph`: the reusable transfer every part
  of Stacks 050J goes through, and
  `AlgebraicGeometry.Stack.hasRelativeProperty_section_of_graph`, the same stated through the
  abbreviation of Stacks 03YK.
* `AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section`: a section of a quasi-separated
  1-morphism is quasi-compact in the relative sense of Properties of Stacks, Section 04XB. This
  is the relative half of the quasi-compactness assertion of part (5), which becomes that
  assertion in the notion of Stacks 050U through Stacks 050T; that step is
  `AlgebraicGeometry.Stack.isQuasiCompact_section`.

## Implementation notes

The whole content is that a section is, up to the equivalence of the next paragraph, the graph
of itself: for `η : s ≫ f ≅ 𝟙 𝒯` the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` of Stacks 050I has
`Γ_s ≫ π₂ ≅ s`, and `π₂` is an equivalence. So Stacks 0457 carries representability, and
Stacks 0459 any relative property, from the graph — which Stacks 050I supplies — to `s` itself.

That `π₂` is an equivalence is the dual of
`CategoryTheory.TwoFibreProductOver.identityGraphEquivalence`, which says that the 2-fibre
product along an identity *second* leg is its first factor: here the identity is in the first
leg and the product is its second factor. The quasi-inverse is the mediating 1-morphism of
Stacks 0040 for the cone `(F, 𝟭, refl)`, so
`CategoryTheory.TwoFibreProductOver.liftCompSnd` already gives one of the two comparison
isomorphisms on the nose and only the other has to be built.

The Stacks 0459 step runs in the direction the implication
`AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences` does *not* supply: it needs the
equivalence on the target side to point from `𝒳` into the 2-fibre product, and the previous
paragraph gives one the other way. Stacks 003Z (2) turns it round, producing a quasi-inverse
functor that is strictly over the site and has a vertical unit, which is exactly the data of a
based functor and a comparison 2-cell. The two verticality facts are then handed to
`CategoryTheory.IsHomLift.comp_lift_id_left'` positionally rather than by instance search:
the source object of the second factor is spelled through `BasedFunctor.comp`, and instance
resolution unifies at reducible transparency only, where that does not unfold.

Every part of Stacks 050J is one application of
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` to the corresponding assertion of
Stacks 050I, so none of them needs an instance of Stacks 03YK: the properties are written as the
longhand quantifier of Section 04XB, which is the form Stacks 050I supplies them in. The one
exception is the quasi-compactness half of part (5), which is phrased with Stacks 050U rather
than with Section 04XB; Stacks 050T says that for a 1-morphism representable by algebraic spaces
the two notions agree, and part (1) supplies the representability, so
`AlgebraicGeometry.Stack.isQuasiCompact_section` is the relative half
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section` read across that equivalence.

Parts (3), (4) and (5) are read at the notions of Properties of Stacks, Section 04XB, as they are
in Stacks 050I and Stacks 050H. Part (4) is not read at Stacks 0CL5 — properness of `s` as a
1-morphism of algebraic stacks, i.e. separated, of finite type and universally closed — which
would need Stacks 0512, the diagonal conditions of Stacks 04YS and the locally-of-finite-type
half of part (1). That is a different statement from the one Stacks 050I supplies, and since the source proves Stacks 050J by specialising
Stacks 050I its conclusions are the conclusions of Stacks 050I; part (4) is therefore
`AlgebraicGeometry.Stack.isRelativelyProper_section`. The locally-of-finite-type half of part (1)
is in the library in any case, by way of the same half of Stacks 050H in
`StacksFrontier/AlgebraicGeometry/Stacks/FibreProductComparisonFiniteType.lean`.

## References

* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v u v₁ u₁ v₂ u₂

variable {C : Type u} [Category.{v} C] {A : Type u₁} [Category.{v₁} A]
  {X : Type u₂} [Category.{v₂} X]

/-- **The 2-fibre product along an identity first leg, as a functor out of the second factor.**
For a functor `F : X ⥤ A` over `C`, an object of `X` determines the object of
`A ×_{𝟭 A, A, F} X` with components its image and itself and with identity comparison
isomorphism. It is the mediating 1-morphism of Stacks 0040 for the cone `(F, 𝟭 X, refl)`. -/
def identityFstGraphFunctor (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A) (hF : F ⋙ pA = pX) :
    X ⥤ TwoFibreProductOver pA pX pA (𝟭 A) F :=
  lift pA pX pA (𝟭 A) F pX F (𝟭 X) hF (Functor.id_comp pX) (Iso.refl F)
    (fun x => IsHomLift.id (Functor.congr_obj hF x))

/-- The second projection undoes
`CategoryTheory.TwoFibreProductOver.identityFstGraphFunctor` on the nose: that is
`CategoryTheory.TwoFibreProductOver.liftCompSnd` for the cone defining it. -/
theorem identityFstGraphFunctor_comp_snd (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A)
    (hF : F ⋙ pA = pX) :
    identityFstGraphFunctor pA pX F hF ⋙ snd pA pX pA (𝟭 A) F = 𝟭 X :=
  rfl

/-- The morphism of `A ×_{𝟭 A, A, F} X` from an object to its image under
`π₂ ⋙ identityFstGraphFunctor`: the comparison isomorphism in the first component and the
identity in the second. -/
def identityFstGraphUnitHom (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A) (hF : F ⋙ pA = pX)
    (P : TwoFibreProductOver pA pX pA (𝟭 A) F) :
    P ⟶ (snd pA pX pA (𝟭 A) F ⋙ identityFstGraphFunctor pA pX F hF).obj P where
  hbase := eqToHom P.hy.symm
  a := P.iso.hom
  b := 𝟙 P.y
  ha := by
    have hv : pA.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    refine IsHomLift.of_fac' pA (eqToHom P.hy.symm) P.iso.hom P.hx
      (Functor.congr_obj hF P.y) ?_
    have hfac := IsHomLift.fac' pA (𝟙 P.base) P.iso.hom
    simpa [Category.assoc, eqToHom_trans] using hfac
  hb := IsHomLift.of_fac pX (eqToHom P.hy.symm) (𝟙 P.y) P.hy rfl (by simp)
  w := by
    change P.iso.hom ≫ 𝟙 (F.obj P.y) = P.iso.hom ≫ F.map (𝟙 P.y)
    simp

/-- `CategoryTheory.TwoFibreProductOver.identityFstGraphUnitHom` is an isomorphism: both of its
components are. -/
theorem isIso_identityFstGraphUnitHom (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A)
    (hF : F ⋙ pA = pX) (P : TwoFibreProductOver pA pX pA (𝟭 A) F) :
    IsIso (identityFstGraphUnitHom pA pX F hF P) := by
  apply isIso_of_isIso_components pA pX pA (𝟭 A) F (identityFstGraphUnitHom pA pX F hF P)
  · show IsIso P.iso.hom
    infer_instance
  · show IsIso (𝟙 P.y)
    infer_instance

/-- **The 2-fibre product along an identity first leg is its second factor.** The second
projection `A ×_{𝟭 A, A, F} X ⟶ X` is an equivalence, with inverse
`CategoryTheory.TwoFibreProductOver.identityFstGraphFunctor`: the unit sends an object to its
own comparison isomorphism, which is the only non-identity datum. -/
noncomputable def identityFstGraphEquivalence (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A)
    (hF : F ⋙ pA = pX) :
    TwoFibreProductOver pA pX pA (𝟭 A) F ≌ X := by
  refine CategoryTheory.Equivalence.mk (snd pA pX pA (𝟭 A) F)
    (identityFstGraphFunctor pA pX F hF) (NatIso.ofComponents
      (fun P => haveI := isIso_identityFstGraphUnitHom pA pX F hF P
      asIso (identityFstGraphUnitHom pA pX F hF P)) ?_) (Iso.refl _)
  intro P Q φ
  apply Hom.ext'
  · change φ.a ≫ Q.iso.hom = P.iso.hom ≫ F.map φ.b
    simpa [Functor.id_map] using φ.w
  · change φ.b ≫ 𝟙 Q.y = 𝟙 P.y ≫ φ.b
    simp

/-- The second projection of a 2-fibre product whose first leg is an identity is an
equivalence. -/
theorem snd_isEquivalence_identityFst (pA : A ⥤ C) (pX : X ⥤ C) (F : X ⥤ A)
    (hF : F ⋙ pA = pX) :
    (snd pA pX pA (𝟭 A) F).IsEquivalence :=
  (identityFstGraphEquivalence pA pX F hF).isEquivalence_functor

end CategoryTheory.TwoFibreProductOver

open CategoryTheory AlgebraicGeometry CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- The second projection of `𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is an equivalence on underlying categories:
its first leg is an identity, so
`CategoryTheory.TwoFibreProductOver.snd_isEquivalence_identityFst` applies. -/
theorem sectionSecondProjection_isEquivalence (f : 𝒳 ⟶ 𝒯) :
    (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom.toFunctor.IsEquivalence :=
  TwoFibreProductOver.snd_isEquivalence_identityFst 𝒯.val.val.p 𝒳.val.val.p
    f.hom.hom.toFunctor f.hom.hom.w

/-- The 2-isomorphism `s ≅ Γ_s ≫ π₂` supplied by Stacks 050I, read as an isomorphism in the
category of based functors `𝒯 ⥤ᵇ 𝒳`. Writing it out rather than using `asIso` makes its inverse
the based 2-cell `(graph_snd_iso ..).inv` on the nose, which is what the verticality of the
inverse is read off. -/
noncomputable def sectionGraphSndBasedIso (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (η : s ≫ f ≅ 𝟙 𝒯) :
    s.hom.hom ≅ BasedFunctor.comp (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom
      (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom where
  hom := (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).hom.hom.hom
  inv := (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom
  hom_inv_id :=
    congrArg (fun q => q.hom.hom) (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).hom_inv_id
  inv_hom_id :=
    congrArg (fun q => q.hom.hom) (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv_hom_id

/-- **Stacks 050J, part (1), representability half.** A section of a 1-morphism of algebraic
stacks is representable by algebraic spaces.

The graph of `s` over `𝒯`, taken for the cospan `(𝟙 𝒯, f)`, is representable by algebraic spaces
by Stacks 050I, and `s` is 2-isomorphic to its composite with the second projection, which is an
equivalence by `AlgebraicGeometry.Stack.sectionSecondProjection_isEquivalence`. Stacks 0457
carries representability across that square. -/
@[stacks 050J "part (1): representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳)
    (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯)) :
    IsRepresentableByAlgebraicSpaces B S hS s.hom.hom := by
  obtain ⟨η⟩ := hs
  exact (@isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS _ _ _ _
    (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom s.hom.hom (BasedFunctor.id 𝒯.val.val)
    (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom
    (BasedNatIso.mkNatIso
      ((BasedNatTrans.forgetful 𝒯.val.val 𝒳.val.val).mapIso
        (sectionGraphSndBasedIso B S hS f s η))
      (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).hom.hom.hom.isHomLift')
    (inferInstanceAs (Functor.IsEquivalence (𝟭 𝒯.val.val.obj)))
    (sectionSecondProjection_isEquivalence B S hS f)).mpr
      (isRepresentableByAlgebraicSpaces_graph B S hS s (𝟙 𝒯) f η.symm)

/-- **Any relative property of the graph of a section transfers to the section, with no
hypothesis on the property.** Stacks 0459 at the 2-commutative square identifying `s` with
`Γ_s ≫ π₂`, read in the direction opposite to the one
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` supplies: the equivalence on the
target side has to be a 1-morphism `𝒳 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` over the site, and
`AlgebraicGeometry.Stack.sectionSecondProjection_isEquivalence` only gives one the other way.
Stacks 003Z (2) turns it round: the quasi-inverse functor it produces is strictly over the site
and its unit is vertical, so it is a based functor and the comparison 2-cell is the given
2-isomorphism whiskered with that unit.

The property is written out as the quantifier of Stacks 03YK, which is the form the properties
of Properties of Stacks, Section 04XB are stated with, so neither stability under base change
nor locality at the target has to be in scope. -/
theorem relativeProperty_section_of_graph (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (η : s ≫ f ≅ 𝟙 𝒯)
    (hg : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.obj)
      (_hy : y ⋙ (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒯.val.val.p
          (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p y
          (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒯.val.val.p 𝒳.val.val.p y
          s.hom.hom.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  obtain ⟨F, hF, u, c, hu, _hc⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p 𝒳.val.val.p
    (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.property 𝒳.val.property
    (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom.toFunctor
    (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom.w
    (sectionSecondProjection_isEquivalence B S hS f)
  have hFequiv : Functor.IsEquivalence F :=
    (CategoryTheory.Equivalence.mk
      (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒯) f).snd.hom.hom.toFunctor F
      u.symm c).isEquivalence_inverse
  let hαfun : (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor ≅ s.hom.hom.toFunctor ⋙ F :=
    (Functor.isoWhiskerLeft (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor u.symm).trans
      (Functor.isoWhiskerRight
        ((BasedNatTrans.forgetful 𝒯.val.val 𝒳.val.val).mapIso
          (sectionGraphSndBasedIso B S hS f s η)).symm F)
  have hvert : ∀ t : 𝒯.val.val.obj,
      (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.IsHomLift
        (𝟙 (𝒯.val.val.p.obj t)) (hαfun.hom.app t) := by
    intro t
    have h₁ : (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.IsHomLift
        (𝟙 ((twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.obj
          ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)))
        (u.inv.app ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)) := by
      have hhom : (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.IsHomLift
          (𝟙 ((twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.obj
            ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)))
          (u.app ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)).hom :=
        hu ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)
      exact IsHomLift.lift_id_inv _ _
        (u.app ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t))
    have h₂ : 𝒳.val.val.p.IsHomLift (𝟙 (𝒯.val.val.p.obj t))
        ((graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom.app t) :=
      (graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom.isHomLift' t
    have h₃ : (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.IsHomLift
        (𝟙 (𝒯.val.val.p.obj t))
        (F.map ((graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom.app t)) :=
      Functor.isHomLift_map_of_comp_eq hF (𝟙 (𝒯.val.val.p.obj t))
        ((graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom.app t)
    -- The two verticality facts are supplied positionally rather than by instance search: the
    -- source of the second factor is spelled through `BasedFunctor.comp`, and instance
    -- resolution unifies at reducible transparency only, where that does not unfold.
    exact @IsHomLift.comp_lift_id_left' _ _ _ _
      (twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p _ _ _
      ((twoFibreProductAlgebraicStack B S hS (𝟙 𝒯) f).val.val.p.obj
        ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t))
      (u.inv.app ((graph B S hS s (𝟙 𝒯) f η.symm).hom.hom.toFunctor.obj t)) h₁ _ _
      (𝟙 (𝒯.val.val.p.obj t))
      (F.map ((graph_snd_iso B S hS s (𝟙 𝒯) f η.symm).inv.hom.hom.app t)) h₃
  exact @relativeProperty_of_equivalences B S hS _ _ _ _ P
    s.hom.hom (graph B S hS s (𝟙 𝒯) f η.symm).hom.hom (BasedFunctor.id 𝒯.val.val)
    { toFunctor := F, w := hF } (BasedNatIso.mkNatIso hαfun hvert)
    (inferInstanceAs (Functor.IsEquivalence (𝟭 𝒯.val.val.obj))) hFequiv hg

/-- `AlgebraicGeometry.Stack.relativeProperty_section_of_graph` stated through the abbreviation
`AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK. The two instance hypotheses of that
abbreviation are not used by the argument; they are in scope because the statement mentions it. -/
theorem hasRelativeProperty_section_of_graph (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (η : s ≫ f ≅ 𝟙 𝒯)
    (hg : HasRelativeProperty B S hS P (graph B S hS s (𝟙 𝒯) f η.symm).hom
      (isRepresentableByAlgebraicSpaces_graph B S hS s (𝟙 𝒯) f η.symm)) :
    HasRelativeProperty B S hS P s.hom
      (isRepresentableByAlgebraicSpaces_section B S hS f s ⟨η⟩) :=
  relativeProperty_section_of_graph B S hS P f s η hg

/-- **Stacks 050J, part (1), locally-of-finite-type half.** A section of a 1-morphism of
algebraic stacks is locally of finite type, in the sense of Properties of Stacks, Section 04XB.

By the locally-of-finite-type half of Stacks 050I part (1) the graph
`Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is locally of finite type, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries that to `s`. No hypothesis on
`f` is needed, exactly as in Stacks 050I and Stacks 050H. Together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_section` this is the whole of
part (1). -/
@[stacks 050J "part (1): locally of finite type"]
theorem isLocallyOfFiniteType_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳)
    (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯)) :
    IsLocallyOfFiniteType B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k.hom) f s η
    (isLocallyOfFiniteType_graph B S hS s (𝟙 𝒯) f η.symm)

/-- **Stacks 050J, part (2).** If `f : 𝒳 ⟶ 𝒯` is Deligne–Mumford then a section of `f` is
unramified, in the relative sense of Stacks 03YK.

By Stacks 050I part (2) the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is unramified, and
`AlgebraicGeometry.Stack.hasRelativeProperty_section_of_graph` carries that to `s`. The two
instance arguments of Stacks 03YK are Stacks 03ZJ and Stacks 042A composed with the comparison
of the fppf and fpqc precoverages. -/
@[stacks 050J "part (2): unramified"]
theorem isUnramified_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : IsDM B S hS f) :
    letI : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom) :=
      Space.isUnramified_isStableUnderBaseChange B S hS
    letI : MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsUnramified B S hS k.hom)
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
        (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
    HasRelativeProperty B S hS
      (fun _ _ k => Space.IsUnramified B S hS k.hom)
      s.hom (isRepresentableByAlgebraicSpaces_section B S hS f s hs) := by
  obtain ⟨η⟩ := hs
  let := Space.isUnramified_isStableUnderBaseChange B S hS
  let := (Space.isUnramified_isLocalAtTarget_fpqc B S hS).of_le
    (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact hasRelativeProperty_section_of_graph B S hS _ f s η
    (isUnramified_graph B S hS s (𝟙 𝒯) f η.symm hf)

/-- **Stacks 050J, part (3).** If `f : 𝒳 ⟶ 𝒯` is quasi-DM then a section of `f` is locally
quasi-finite, in the sense of Properties of Stacks, Section 04XB.

By Stacks 050I part (3) the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is locally quasi-finite, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries that to `s`. One statement
suffices: Stacks 050I already takes the quasi-DM condition of Stacks 04YW apart, so the input is
local quasi-finiteness alone. The property is the longhand lambda rather than the packaged local
quasi-finiteness of Stacks 06MF, so no instance of Stacks 03YK is needed. -/
@[stacks 050J "part (3): locally quasi-finite"]
theorem isLocallyQuasiFinite_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) :
    IsLocallyQuasiFinite B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsLocallyQuasiFinite B S hS k.hom) f s η
    (isLocallyQuasiFinite_graph B S hS s (𝟙 𝒯) f η.symm hf)

/-- **Stacks 050J, part (4).** If `f : 𝒳 ⟶ 𝒯` is separated then a section of `f` is proper in
the sense of Properties of Stacks, Section 04XB.

By Stacks 050I part (4) the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is proper, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries that to `s`. The separatedness
condition of Stacks 04YW is a single property of the relative diagonal, so there is no
conjunction to project here. The property is the longhand lambda rather than
`AlgebraicGeometry.Space.properProperty`, so the fppf
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instance of Stacks 0422 is not needed — which
matters here, because this library does not have it.

Properness is read in the sense of Section 04XB, as it is in Stacks 050I part (4)
(`AlgebraicGeometry.Stack.isProper_graph`) and in Stacks 050H part (6)
(`AlgebraicGeometry.Stack.isProper_comparison`). That is the reading the source's own proof
forces: Stacks 050J is a special case of Stacks 050I, so its conclusions are the conclusions of
Stacks 050I, and `s` carries the Section 04XB notions because part (1) makes it representable by
algebraic spaces. Reading part (4) at Stacks 0CL5 instead would assert properness of `s` as a
1-morphism of algebraic stacks, which is a different statement from the one Stacks 050I
supplies. -/
@[stacks 050J "part (4): proper"]
theorem isRelativelyProper_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : AlgebraicStacks.IsSeparated B S hS f) :
    IsProper B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsProper B S hS k.hom) f s η
    (isProper_graph B S hS s (𝟙 𝒯) f η.symm hf)

/-- **The relative half of Stacks 050J, part (5), quasi-compactness.** If `f : 𝒳 ⟶ 𝒯` is
quasi-separated then a section of `f` is quasi-compact in the sense of Properties of Stacks,
Section 04XB.

This is *not* the quasi-compactness half of part (5) of Stacks 050J, which asserts
quasi-compactness of the section in the sense of Stacks 050U — every base change by a
quasi-compact algebraic stack is a quasi-compact algebraic stack. That statement is
`AlgebraicGeometry.Stack.isQuasiCompact_section`, this one read across Stacks 050T.

By Stacks 050I part (5) the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is quasi-compact, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries that to `s`. A single
statement suffices: Stacks 050I takes the quasi-separatedness condition of Stacks 04YW apart, so
the input is quasi-compactness alone. -/
theorem isRelativelyQuasiCompact_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    IsQuasiCompact B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsQuasiCompact B S hS k.hom) f s η
    (isQuasiCompact_graph B S hS s (𝟙 𝒯) f η.symm hf)

/-- **Stacks 050J, part (5), quasi-compactness half.** If `f : 𝒳 ⟶ 𝒯` is quasi-separated then a
section of `f` is quasi-compact in the sense of Stacks 050U: every base change of it by a
quasi-compact algebraic stack is again a quasi-compact algebraic stack.

The section is representable by algebraic spaces by part (1), and quasi-compact in the relative
sense of Properties of Stacks, Section 04XB by
`AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section`. Stacks 050T identifies the two
notions for a 1-morphism representable by algebraic spaces, and that is the whole step. -/
@[stacks 050J "part (5): quasi-compact"]
theorem isQuasiCompact_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    IsQuasiCompactMorphism B S hS s :=
  (isQuasiCompact_iff_baseChange_quasiCompact B S hS s
      (isRepresentableByAlgebraicSpaces_section B S hS f s hs)).mp
    (isRelativelyQuasiCompact_section B S hS f s hs hf)

/-- **Stacks 050J, part (5), quasi-separatedness half.** If `f : 𝒳 ⟶ 𝒯` is quasi-separated then
a section of `f` is quasi-separated, in the sense of Properties of Stacks, Section 04XB.

By Stacks 050I part (5) the graph `Γ_s : 𝒯 ⟶ 𝒯 ×_{𝟙 𝒯, 𝒯, f} 𝒳` is quasi-separated, and
`AlgebraicGeometry.Stack.relativeProperty_section_of_graph` carries that to `s`. A single
statement suffices, because Stacks 050I already projects the conjunction of Stacks 04YW
quasi-separatedness: the input is quasi-separatedness alone. The quasi-compactness half of
part (5) is `AlgebraicGeometry.Stack.isQuasiCompact_section`, which reads the Section 04XB
assertion `AlgebraicGeometry.Stack.isRelativelyQuasiCompact_section` across Stacks 050T into the
notion of Stacks 050U. -/
@[stacks 050J "part (5): quasi-separated"]
theorem isQuasiSeparated_section (f : 𝒳 ⟶ 𝒯) (s : 𝒯 ⟶ 𝒳) (hs : Nonempty (s ≫ f ≅ 𝟙 𝒯))
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS s.hom := by
  obtain ⟨η⟩ := hs
  exact relativeProperty_section_of_graph B S hS
    (fun _ _ k => Space.IsQuasiSeparated B S hS k.hom) f s η
    (isQuasiSeparated_graph B S hS s (𝟙 𝒯) f η.symm hf)

end AlgebraicGeometry.Stack

end
