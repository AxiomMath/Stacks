module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Flat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.RingTheory.Rig.FiniteType

/-!
# Flatness in the Bootstrap sense implies flatness of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCG** says that if `f` is
representable by algebraic spaces and flat in the Bootstrap sense of Stacks 03XZ, then `f` is
flat in the sense of Definition 0GCC.

The source's proof has three steps. For a commutative square with `U`, `V` affine formal
algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by algebraic spaces and étale, write
`U ⟶ V` as `Spf (φ)` for a continuous homomorphism `φ : A ⟶ C` of adic Noetherian topological
rings.

1. `U ⟶ V` is flat in the Bootstrap sense. This is where Stacks 05B9 is used: for a scheme
   `T ⟶ V`, flatness of `X ×_Y T ⟶ T` gives flatness of `U ×_Y T ⟶ T` because `U ⟶ X` is
   étale hence flat and flat morphisms compose, `U ×_Y T = U ×_V (V ×_Y T)` identifies the
   source, and Stacks 05B9 replaces the base `Y` by the étale intermediate `V`.
2. For every weak ideal of definition `I` of `A` the ring map `A ⧸ I → C ⧸ J(I)` is flat,
   where `J(I)` is the closure of `φ(I)C`. This is the step proved here: `φ` is taut, so the
   square with vertices `Spec (C ⧸ J(I))`, `Spec (A ⧸ I)`, `Spf C` and `Spf A` is cartesian
   by `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`, and
   reading the base-changed flatness condition on the identity étale chart of that stage map
   gives flatness of the morphism of affine schemes it is.
3. `φ` itself is flat, by Stacks 0912.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatULift` and `AlgebraicGeometry.Space.flatPropertyULift`:
  flatness of a morphism of algebraic spaces over `S` with values in a larger universe, as the
  condition on every étale scheme chart and as a property of morphisms, which is what the
  Bootstrap condition of Stacks 03XZ is tested with here.
* `AlgebraicGeometry.FormalSpace.IsTautOnEveryChartMap`,
  `AlgebraicGeometry.FormalSpace.FlatnessDescendsToChartSpectra` and
  `TopologicalRing.IsFlatOfFlatModuloEveryWeakIdeal`: the three inputs of steps 1 and 3 that
  this library does not carry, each named once with the Stacks tag it is.

## Main results

* `AlgebraicGeometry.FormalSpace.flat_quotientMap_of_flatULift_formalSpectrumMap`: step 2, the
  stage half of Stacks 0GCG.

## Implementation notes

Step 2 is the same argument as the stage half of Stacks 0ANT,
`AlgebraicGeometry.FormalSpace.finiteType_quotientMap_of_isFiniteType_formalSpectrumMap`, with
flatness in place of being locally of finite type: paste the cartesian stage square against
the comparison isomorphism between a represented presheaf and the underlying presheaf of its
sheafification, read the Bootstrap condition at the scheme-valued point of `Spf A` cut out by
`Spec (A ⧸ I)`, transport it along the pasting isomorphism, and evaluate the resulting
every-étale-chart condition on the identity charts of the stage map. Flatness of the morphism
of affine schemes so obtained is flatness of the ring map by
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`.

Three inputs are explicit hypotheses because the library does not carry them.

* `htaut` is tautness of the homomorphism presenting each chart map. It is the implication
  (1) ⟹ (3) of Stacks 0AN5, reached from representability of `f` through the implication
  (4) ⟹ (1) of Stacks 0ANK; the library carries only the implication (2) ⟹ (1) of Stacks
  0AN5, `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
  whose missing converse rests on Stacks 0AKN. No declaration in this library concludes
  `RingHom.IsTaut` of the homomorphism presenting a chart map.
* `hdescend` is step 1. It consumes the Bootstrap flatness of `f` and returns that of the
  formal spectrum map presenting a chart map, which is how Stacks 05B9 enters; the library
  carries Stacks 05B9 only pointwise for schemes
  (`AlgebraicGeometry.isFlatOverAt_comp_iff_of_etale`) and carries neither flatness as a
  property of morphisms of universe-lifted algebraic spaces stable under composition and base
  change nor the fibre product identification `U ×_Y T = U ×_V (V ×_Y T)` for them.
* `hlimit` is step 3, Stacks 0912 in the form the proof uses it. The library carries Stacks
  0912 as `flat_limit_and_tensor_limit_of_flat_quotients`, for an inverse system of modules;
  deducing the statement about `φ` from it needs the identification of `C` with the limit of
  its own quotients `C ⧸ J(I)`, which this library does not carry.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCG](https://stacks.math.columbia.edu/tag/0GCG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Flatness of a morphism of presheaves with values in a universe `max w u` independent of
the universe `u` of the schemes: every commuting square of étale scheme charts induces a flat
morphism of schemes. This is `AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift` with
flatness in place of being locally of finite type. -/
abbrev IsFlatULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) : Prop :=
  HoldsOnEveryEtaleChartULift.{w} B S hS
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) f

/-- Flatness, as a property of morphisms in the category of algebraic spaces over `S` with
values in `Type (max w u)`. This is the property with which the Bootstrap condition of Stacks
03XZ is tested in Stacks 0GCG. -/
abbrev flatPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsFlatULift.{w} B S hS f.hom

end AlgebraicGeometry.Space

namespace TopologicalRing

universe u

/-- **Stacks 0912** in the form the proof of Stacks 0GCG uses it: a taut continuous
homomorphism of Noetherian adic topological rings which is flat modulo every weak ideal of
definition of its source is flat. The library carries Stacks 0912 as
`flat_limit_and_tensor_limit_of_flat_quotients`, a statement about an inverse system of
modules; passing from it to this one needs the identification of the target with the limit of
its own quotients by the closed extensions of the weak ideals of definition of the source,
which this library does not carry. -/
abbrev IsFlatOfFlatModuloEveryWeakIdeal : Prop :=
  ∀ {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C] (φ : A →+* C),
    TopologicalRing.IsAdic A → TopologicalRing.IsAdic C → Continuous φ → RingHom.IsTaut φ →
    (∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
        (Ideal.map_le_iff_le_comap.mp subset_closure)).Flat) →
    φ.Flat

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs this library does not carry -/

/-- Tautness of the homomorphism presenting each affine representable étale chart map of a
morphism of formal algebraic spaces over `S`. This is the implication (1) ⟹ (3) of **Stacks
0AN5**, reached from representability of the morphism through the implication (4) ⟹ (1) of
Stacks 0ANK. The library carries only the implication (2) ⟹ (1) of Stacks 0AN5, whose
converse rests on Stacks 0AKN, and no declaration in it concludes `RingHom.IsTaut` of such a
homomorphism. The binders are those of `AlgebraicGeometry.FormalSpace.IsFlat`. -/
abbrev IsTautOnEveryChartMap {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (U V : FppfSheaf B S hS)
    (_hU : IsAffineFormalAlgebraicSpace B S hS U)
    (_hV : IsAffineFormalAlgebraicSpace B S hS V)
    (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
    (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom),
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a.hom ha →
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) b.hom hb →
      a ≫ f = t ≫ b → ∀ (A C : Type u)
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
          [IsNoetherianRing A]
        [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
          [IsNoetherianRing C],
        TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
        ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
          (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
          (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
          t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
            RingHom.IsTaut g.toRingHom

/-- The geometric step of **Stacks 0GCG**: Bootstrap flatness of a morphism of formal
algebraic spaces over `S` descends to the formal spectrum map presenting any of its affine
representable étale chart maps. This is where Stacks 05B9 enters the source's proof, together
with flatness of an étale morphism, stability of flatness under composition and base change,
and the identification `U ×_Y T = U ×_V (V ×_Y T)`. The library carries Stacks 05B9 only
pointwise for schemes and carries none of the others for morphisms of universe-lifted
algebraic spaces. -/
abbrev FlatnessDescendsToChartSpectra : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom),
    Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS)
      f.hom hrep →
    ∀ (U V : FppfSheaf B S hS)
      (_hU : IsAffineFormalAlgebraicSpace B S hS U)
      (_hV : IsAffineFormalAlgebraicSpace B S hS V)
      (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
      (ha : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS a.hom)
      (hb : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS b.hom),
      Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) a.hom ha →
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) b.hom hb →
        a ≫ f = t ≫ b → ∀ (A C : Type u)
          [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
            [IsNoetherianRing A]
          [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
            [IsNoetherianRing C],
          TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
          ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
            (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
            (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
            t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
              ∃ hrep' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
                  (formalSpectrumMap hA g).hom,
                Space.HasPropertyULift.{u + 1} B S hS
                  (Space.flatPropertyULift.{u + 1} B S hS) (formalSpectrumMap hA g).hom hrep'

/-! ### The stage half -/

variable {B S hS}
variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **The stage half of Stacks 0GCG.** Let `φ : A ⟶ C` be a taut continuous homomorphism of
weakly admissible topological rings over `S`. If `Spf (φ)` is representable by algebraic
spaces and flat in the Bootstrap sense, then for every weak ideal of definition `I` of `A` the
induced ring map `A ⧸ I → C ⧸ J(I)`, with `J(I)` the closure of `φ(I)C`, is flat.

Tautness makes the square formed by the two thickening stages and `Spf (φ)` cartesian, so the
stage map is a base change of `Spf (φ)` and inherits flatness; reading that condition on the
identity étale charts of the stage map returns flatness of the morphism of affine schemes it
is, which is flatness of the ring map. -/
theorem flat_quotientMap_of_flatULift_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hA f).hom)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS)
      (formalSpectrumMap hA f).hom hrep)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).Flat := by
  obtain ⟨⟨Kv, hKw⟩, hKeq, hIK, hsq⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E f hf ⟨I, hI⟩
  subst hKeq
  set G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) with hG
  set k := (BigAffineFppf.inclusion B S hS).map
    (f.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map f.toRingHom), hKw⟩ hIK) with hk
  have hright := hsq.map G
  have hleft : IsPullback (sheafifiedYonedaObjIso B S hS _).hom ((uliftYoneda.{u + 1}).map k)
      (G.map ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k))
      (sheafifiedYonedaObjIso B S hS _).hom :=
    IsPullback.of_horiz_isIso ⟨(sheafifiedYonedaObjIso_naturality B S hS k).symm⟩
  have hpaste := hleft.paste_horiz hright
  have hfl : Space.IsFlatULift.{u + 1} B S hS
      (pullback.fst ((sheafifiedYonedaObjIso B S hS
          ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))).hom ≫
        G.map (formalSpectrumInclusion D ⟨I, hI⟩)) (G.map (formalSpectrumMap hA f))) :=
    hflat _ _
  have hchart := Space.holdsOnEveryEtaleChartULift_precomp B S hS
    (@AlgebraicGeometry.Flat.{u}) hpaste.flip.isoPullback.hom _ hfl
  have hchart' : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
      (@AlgebraicGeometry.Flat.{u}) ((uliftYoneda.{u + 1}).map k) := by
    rw [← hpaste.flip.isoPullback_hom_fst]
    exact hchart
  have hk' := prop_of_holdsOnEveryEtaleChartULift B S hS k hchart'
  rw [hk] at hk'
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp
    (show AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom hIK))) from hk')

end AlgebraicGeometry.FormalSpace

end
