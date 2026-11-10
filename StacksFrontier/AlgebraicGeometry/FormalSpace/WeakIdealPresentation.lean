module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.CategoryTheory.Sites.Representable.MapsFromRepresentable
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weak-ideal presentations of an affine formal algebraic space (Stacks 0AIC)

Let `A` be a weakly admissible topological ring and let the fppf sheaf `X` be presented as the
colimit of the spectra of the quotients of `A` by its weak ideals of definition — that is,
condition (1) of **Stacks 0AIC**, recorded by
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation`.

This file proves two things about that situation.

First, the *rigidity* of the presentation: any other presentation of `X` by affine thickenings
is again a presentation by quotients of `A`. Each of its stages is the spectrum of a quotient
`A ⧸ Jᵢ` by a weak ideal of definition, compatibly with all transition morphisms and with both
colimit descriptions of `X`, and those ideals are cofinal among all weak ideals of definition.
That is `presentation_quotients_cofinal`, which is the engine of the proof of Stacks 0AIC. Its
proof is the one mapped out in the Stacks text: an affine stage of either presentation is
quasi-compact, hence factors through a stage of the other (Stacks 0AIA, in the hypothesis-free
form of `AlgebraicGeometry.exists_factor_through_thickening`), and the comparison morphism obtained
this way is a thickening, so by Stacks 0AIC's closed-immersion analysis it exhibits the stage as
`Spec (A ⧸ J)` for a weak ideal of definition `J`.

Second, the implication **(1) ⇒ (5)** of Stacks 0AIC. The transition morphisms of the canonical
weak-ideal presentation are thickenings, because an element of a weak ideal of definition is
topologically nilpotent and so becomes nilpotent modulo any smaller — hence open — one; this
makes `X` an affine formal algebraic space. For the section rings, rigidity identifies the stage
`Γ(Xᵢ, 𝒪)` of an arbitrary presentation with `A ⧸ Jᵢ` compatibly with the transition maps, so the
compatible family of the classes of a single element of `A` lifts any prescribed section of a
single stage, and the projections `lim Γ(Xᵢ, 𝒪) → Γ(Xᵢ, 𝒪)` are surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.presentation_quotients_cofinal`: every presentation by affine
  thickenings of a formal spectrum comes from a cofinal system of weak ideals of definition.
* `AlgebraicGeometry.FormalSpace.weak_quotient_transition_isThickening`: every transition
  morphism of a weak-ideal presentation is a thickening.
* `AlgebraicGeometry.FormalSpace.hasThickeningPresentation_of_weakIdealColimitPresentation`: a
  sheaf with a weak-ideal presentation has a presentation by affine thickenings, with no
  condition on the size of the site.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_weakIdealColimitPresentation`:
  a sheaf with a weak-ideal presentation is an affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_weakIdealColimitPresentation`:
  the section-ring projections of *any* presentation by affine thickenings are then surjective.
* `AlgebraicGeometry.FormalSpace.hasAllSurjectivePresentations_of_weakIdealColimitPresentation`
  and `AlgebraicGeometry.FormalSpace.hasAllSurjectivePresentations_of_exists_weaklyAdmissible`:
  condition (1) of Stacks 0AIC implies condition (5), the latter stated with condition (1) in
  the existential form in which Stacks 0AIC uses it.

## Implementation notes

The tag `0AIC` names the equivalence of the five conditions and is spread over the declarations
that prove its separate clauses, each registration naming the clause it carries; the one proved
here is (1) ⇒ (5).

The weak ideals of definition of a ring in `Type u` form a `Type u`, whereas the index of a
presentation in `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace` lives in
`Type (u + 1)`, one universe above the schemes; `weakIdealsULiftEquivalence` is the universe
lift, and the colimit is transported along it with
`CategoryTheory.Limits.HasColimit.isoOfEquivalence`.

Surjectivity of a section projection is proved by exhibiting a preimage, not by identifying the
inverse limit with `A`: the stage identifications turn the projection into `A ⧸ Jᵢ`-valued
reduction, and `A → A ⧸ Jᵢ` is surjective. In particular no completeness of `A` is used, and
cofinality of the system `Jᵢ` — which `presentation_quotients_cofinal` also supplies — is not
needed for this implication.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

universe v w w₁ w₂

/-- A closed immersion of affine objects of the site gives a monomorphism of represented sheaves. -/
private theorem mono_sheafifiedYoneda_map_of_closedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} (g : U ⟶ V)
    (hg : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map g)) :
    Mono ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map g)) := by
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
    ((BigAffineFppf.inclusion B S hS).map g)) := hg
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying _ (BigFppfOver.toScheme B S hS) _
    inferInstance

/-- If the transition morphisms are closed immersions, each colimit injection of the represented
sheaves is a monomorphism. -/
private theorem mono_colimit_ι_of_closedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type w₁) [Preorder I] [Small.{u + 1} I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (i : I) :
    Mono (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) :=
  Sheaf.mono_colimit_ι_of_mono_transition _
    (fun _ _ g => mono_sheafifiedYoneda_map_of_closedImmersion B S hS (D.map g) (hD g)) i

/-- The identity of a represented presheaf has the property `P` (after pulling it back to schemes)
whenever `P` holds for isomorphisms. -/
private theorem presheaf_id_yoneda_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f], P f) (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro V W g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  have : IsIso ((BigFppfOver.toScheme B S hS).map snd) := Functor.map_isIso _ snd
  exact hP _

/-- A morphism of affine objects of the site commutes with the structure morphisms to `S`. -/
private theorem toScheme_map_comp_structure
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} (g : U ⟶ V) :
    (BigAffineFppf.toScheme B S hS).map g ≫ B.inclusion.map
        ((BigAffineFppf.inclusion B S hS).obj V).hom =
      B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj U).hom := by
  have := congrArg B.inclusion.map (Over.w ((BigAffineFppf.inclusion B S hS).map g))
  rw [B.inclusion.map_comp] at this
  exact this

private theorem exists_factor_through_thickening_no_affine_hypothesis
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type w₁) [Preorder I] [Small.{u + 1} I]
    [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (f : (presheafToSheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u}) ⟶ X) :
    ∃ i : I, ∃ g : (presheafToSheaf (BigFppfOver.topology B S hS)
        (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u}) ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      g ≫ colimit.ι
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫
        e.inv = f := by
  classical
  let J := BigFppfOver.topology B S hS
  let q := BigFppfOver.toScheme B S hS
  obtain ⟨U, a, hUcompact, hasurj, hYEtale⟩ := hYqc
  have hloc := _root_.AlgebraicGeometry.isLocallySurjective_of_surjective_etale B S hS a hasurj
    (hYEtale U (𝟙 (yoneda.obj U))
      (presheaf_id_yoneda_of_isIso B S hS @Etale.{u} (fun _ _ => inferInstance) U))
  let aLift := Functor.whiskerRight a uliftFunctor.{u + 1, u}
  have hlocLift : Presheaf.IsLocallySurjective J aLift :=
    ⟨fun s => J.superset_covering
      (by rintro _ _ ⟨t, ht⟩; exact ⟨ULift.up t, congrArg ULift.up ht⟩)
      (hloc.imageSieve_mem s.down)⟩
  let A := (presheafToSheaf J (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u})
  let p : (Sheaf.sheafifiedYoneda J).obj U ⟶ A :=
    (presheafToSheaf J (Type (u + 1))).map aLift
  have hp : Epi p := (Sheaf.isLocallySurjective_iff_epi p).1
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff J aLift).2 hlocLift)
  let F := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  have htrans : ∀ i j (g : i ⟶ j), Mono (F.map g) := fun i j g =>
    mono_sheafifiedYoneda_map_of_closedImmersion B S hS (D.map g) (hD g)
  let G := (sheafSections J (Type (u + 1))).obj (op U)
  let α : (Sheaf.sheafifiedYoneda J).obj U ⟶ colimit F := p ≫ f ≫ e.hom
  have hbij : Function.Bijective (colimit.post F G) :=
    (Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.1
      (isQuasiCompactObject_over_of_compact_scheme B S hS U) htrans
  obtain ⟨z, hz⟩ := hbij.2 ((Sheaf.sectionEquiv J) α)
  let Fsec := F ⋙ G
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep Fsec (colimit.isColimit Fsec) z
  let gi : (Sheaf.sheafifiedYoneda J).obj U ⟶ F.obj i := (Sheaf.sectionEquiv J).symm x
  have hgi : gi ≫ colimit.ι F i = α := by
    apply (Sheaf.sectionEquiv J).injective
    calc
      (Sheaf.sectionEquiv J) (gi ≫ colimit.ι F i) = (colimit.ι F i).hom.app (op U) x := by
        rw [Sheaf.sectionEquiv_comp]
        exact congrArg ((colimit.ι F i).hom.app (op U))
          ((Sheaf.sectionEquiv J).apply_symm_apply x)
      _ = colimit.post F G (colimit.ι Fsec i x) :=
        (ConcreteCategory.congr_hom (colimit.ι_post F G i) x).symm
      _ = colimit.post F G z := congrArg (colimit.post F G) hx
      _ = (Sheaf.sectionEquiv J) α := hz
  have hmColim : Mono (colimit.ι F i) := mono_colimit_ι_of_closedImmersion B S hS I D hD i
  have : StrongEpi p := strongEpi_of_epi p
  let sq : CommSq gi p (colimit.ι F i) (f ≫ e.hom) := ⟨by simpa [α] using hgi⟩
  obtain ⟨l⟩ := (inferInstance : sq.HasLift).exists_lift
  refine ⟨i, l.l, (cancel_mono e.hom).1 ?_⟩
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact l.fac_right

private theorem exists_factor_from_affine_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : Type w₁) [Preorder D] [Small.{u + 1} D]
    [Nonempty D] [IsDirected D (· ≤ ·)]
    (E : D ⥤ BigAffineFppf B S hS)
    (hE : ∀ ⦃i j : D⦄ (f : i ⟶ j),
      IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map (E.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit
      (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶ X) :
    ∃ i : D, ∃ g : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj U ⟶
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (E.obj i)),
      g ≫ colimit.ι
        (E ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) i ≫ e.inv = f := by
  let q := BigFppfOver.toScheme B S hS
  have hcompact : CompactSpace (q.obj U) := by
    change CompactSpace ((BigAffineFppf.toScheme B S hS).obj
      ⟨U, hU⟩)
    infer_instance
  have hqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj U) := by
    refine ⟨U, 𝟙 _, hcompact, ?_, ?_⟩
    · change (MorphismProperty.presheaf
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) q))
        (𝟙 (yoneda.obj U))
      refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
      intro V W g fst snd hpb
      have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
      have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
      have : IsIso (q.map snd) := Functor.map_isIso _ snd
      exact (inferInstance : Surjective (q.map snd))
    · exact fun _ _ hφ => hφ
  exact exists_factor_through_thickening_no_affine_hypothesis B S hS D E hE X e
    (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) hqc f


private theorem exists_factor_to_stage_of_closedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (D : Type w₁) [Preorder D] [Small.{u + 1} D]
    [Nonempty D] [IsDirected D (· ≤ ·)]
    (E : D ⥤ BigAffineFppf B S hS)
    (hE : ∀ ⦃i j : D⦄ (f : i ⟶ j),
      IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map (E.map f)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit
      (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (V : BigAffineFppf B S hS)
    (f : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ X) :
    ∃ (i : D) (g : V ⟶ E.obj i),
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι
          (E ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)) i ≫ e.inv = f := by
  let U := (BigAffineFppf.inclusion B S hS).obj V
  let q := BigFppfOver.toScheme B S hS
  have hcompact : CompactSpace (q.obj U) := by
    change CompactSpace ((BigAffineFppf.toScheme B S hS).obj V)
    infer_instance
  have hqc : Space.IsQuasiCompactSpace B S hS (yoneda.obj U) := by
    refine ⟨U, 𝟙 _, hcompact, ?_, ?_⟩
    · exact presheaf_id_yoneda_of_isIso B S hS @Surjective.{u} (fun _ _ => inferInstance) U
    · exact fun _ _ hφ => hφ
  obtain ⟨i, g', hg'⟩ := exists_factor_through_thickening_no_affine_hypothesis B S hS D E hE X e
    (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) hqc f
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨g₀, hg₀⟩ := (Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)).map_surjective
    (show F.obj U ⟶ F.obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) from g')
  obtain ⟨g, hg⟩ := Functor.Full.map_surjective (F := BigAffineFppf.inclusion B S hS) g₀
  exact ⟨i, g, by rwa [hg, hg₀]⟩

/-- A transition morphism of the weak-ideal presentation is the map of spectra induced by the
quotient map, up to the stage identifications. -/
private theorem weak_quotient_transition_eq_spec_factor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    {J K : WeakIdeals A} (f : J ⟶ K) :
    (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) =
      (P.quotientIso J).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f))) ≫
        (P.quotientIso K).inv := by
  apply (cancel_mono (P.quotientIso K).hom).1
  simpa using P.quotientIso_natural f

private theorem weak_quotient_transition_closed_immersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    {J K : WeakIdeals A} (f : J ⟶ K) :
    IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom f)))) :=
    IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (show K.1 ≤ J.1 from leOfHom f))
  rw [weak_quotient_transition_eq_spec_factor B S hS A X P f]
  infer_instance

private theorem weak_quotient_colimit_injection_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    [Nonempty (WeakIdeals A)]
    [IsDirected (WeakIdeals A) (· ≤ ·)] (J : WeakIdeals A) :
    Mono (colimit.ι
      (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) J) := by
  exact mono_colimit_ι_of_closedImmersion B S hS _ P.diagram
    (fun _ _ f => weak_quotient_transition_closed_immersion B S hS A X P f) J

private theorem weakIdeals_nonempty
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) : Nonempty (WeakIdeals A) := by
  obtain ⟨J, hJ⟩ := hA.1
  exact ⟨OrderDual.toDual ⟨J, hJ⟩⟩

private theorem weakIdeals_directed
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] :
    IsDirected (WeakIdeals A) (· ≤ ·) := by
  refine ⟨fun J K => ?_⟩
  let L : WeakIdeals A :=
    OrderDual.toDual ⟨J.1 ⊓ K.1, J.2.1.inter K.2.1, fun x hx => J.2.2 x hx.1⟩
  exact ⟨L, show J.1 ⊓ K.1 ≤ J.1 from inf_le_left, show J.1 ⊓ K.1 ≤ K.1 from inf_le_right⟩

/-- If `f = c ≫ g` with `g` a monomorphism, then the square with sides `𝟙 U`, `c`, `f` and `g` is
a pullback square. -/
theorem isPullback_id_of_factorization
    {C : Type u} [Category.{v} C] {U V X : C}
    (c : U ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (h : f = c ≫ g) [Mono g] :
    IsPullback (𝟙 U) c f g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?comm
    (fun s => s.fst) (fun s => by simp) ?snd ?uniq)
  · simp [h]
  · intro s
    apply (cancel_mono g).1
    rw [Category.assoc, ← h]
    exact s.condition
  · intro s m hm₁ hm₂
    simpa using hm₁

/-- If the closed immersion `Spec (R ⧸ I) ⟶ Spec R` is surjective, then `I` is contained in the
nilradical of `R`. -/
theorem ideal_le_nilradical_of_quotient_spec_surjective
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : Function.Surjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base) :
    I ≤ nilradical R := by
  intro x hx
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  obtain ⟨q, hq⟩ := h ⟨p, hp⟩
  have hq' : (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal = p :=
    congrArg PrimeSpectrum.asIdeal hq
  rw [← hq']
  apply Ideal.mem_comap.mpr
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact q.asIdeal.zero_mem

/-- If `K` is a weak ideal of definition of `A` and `H` is an ideal of `A ⧸ K` contained in its
nilradical, then the preimage of `H` in `A` is a weak ideal of definition. -/
theorem weakIdealOfDefinition_comap_of_le_nilradical
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (K : Ideal A) (hK : TopologicalRing.IsWeakIdealOfDefinition K)
    (H : Ideal (A ⧸ K)) (hH : H ≤ nilradical (A ⧸ K)) :
    TopologicalRing.IsWeakIdealOfDefinition (H.comap (Ideal.Quotient.mk K)) := by
  let q := Ideal.Quotient.mk K
  let J := H.comap q
  have hKJ : K ≤ J := fun x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact H.zero_mem
  refine ⟨Ideal.isOpen_of_isOpen_subideal hKJ hK.1, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hH (show q x ∈ H from Ideal.mem_comap.mp hx))
  have hn' : q x ^ (n + 1) = 0 := by
    rw [pow_succ, hn, zero_mul]
  have hmem : x ^ (n + 1) ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [map_pow] using hn'
  exact TopologicalRing.isTopologicallyNilpotent_of_pow (Nat.succ_pos n)
    (hK.2 (x ^ (n + 1)) hmem)

private noncomputable def quotientQuotientEquivComap
    {A : Type u} [CommRing A] (K : Ideal A) (H : Ideal (A ⧸ K)) :
    (A ⧸ H.comap (Ideal.Quotient.mk K)) ≃+* (A ⧸ K) ⧸ H := by
  let φ := (Ideal.Quotient.mk H).comp (Ideal.Quotient.mk K)
  have hker : RingHom.ker φ = H.comap (Ideal.Quotient.mk K) := by
    ext x
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  have hsurj : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

/-- Let `X` be presented as the colimit of the spectra of the quotients of `A` by its weak ideals
of definition. Every thickening `V ⟶ P.diagram.obj K` of a stage of the presentation is, up to
an isomorphism of schemes, the transition morphism from the stage of some weak ideal of
definition `J` containing `K` (that is, `J ≤ K` in the order of `WeakIdeals A`). -/
theorem exists_weakIdeal_over_thickening_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    (K : WeakIdeals A) {V : BigAffineFppf B S hS}
    (f : V ⟶ P.diagram.obj K)
    (hf : Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map f)) :
    ∃ (J : WeakIdeals A) (hJK : J ≤ K)
      (e : (BigAffineFppf.toScheme B S hS).obj V ≅
        (BigAffineFppf.toScheme B S hS).obj (P.diagram.obj J)),
      (BigAffineFppf.toScheme B S hS).map f =
        e.hom ≫ (BigAffineFppf.toScheme B S hS).map
          (P.diagram.map (homOfLE hJK)) := by
  let f' := (BigAffineFppf.toScheme B S hS).map f ≫
    (P.quotientIso K).hom
  have hfclosed : IsClosedImmersion f' := by
    have : IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map f) := hf.1
    exact IsClosedImmersion.comp _ _
  have hquotientIso : Function.Surjective (P.quotientIso K).hom.base :=
    (ConcreteCategory.bijective_of_isIso (P.quotientIso K).hom.base).2
  have hsurj' : Function.Surjective f'.base := by
    change Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map f ≫
        (P.quotientIso K).hom).base)
    rw [Scheme.Hom.comp_base]
    exact hquotientIso.comp hf.2
  obtain ⟨H, e₀, heq⟩ := (IsClosedImmersion.Spec_iff (f := f')).mp hfclosed
  let qSpec := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))
  have hqsurj : Function.Surjective qSpec.base := fun y ↦ by
    obtain ⟨x, hx⟩ := hsurj' y
    refine ⟨e₀.hom.base x, ?_⟩
    rw [← hx, heq, Scheme.Hom.comp_base]
    rfl
  have hHrad := ideal_le_nilradical_of_quotient_spec_surjective H hqsurj
  let J₀ := H.comap (Ideal.Quotient.mk K.1)
  have hJweak := weakIdealOfDefinition_comap_of_le_nilradical K.1 K.2 H hHrad
  let J : WeakIdeals A := OrderDual.toDual ⟨J₀, hJweak⟩
  have hKJ : K.1 ≤ J₀ := fun x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact H.zero_mem
  have hJK : J ≤ K := hKJ
  let qfac : A ⧸ K.1 →+* A ⧸ J₀ :=
    Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom (homOfLE hJK))
  let E := quotientQuotientEquivComap K.1 H
  have hring : CommRingCat.ofHom qfac ≫ E.toCommRingCatIso.hom =
      CommRingCat.ofHom (Ideal.Quotient.mk H) := by
    apply CommRingCat.hom_ext
    ext x
    dsimp only [qfac]
    change E.toRingHom
        (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom (homOfLE hJK))
          (Ideal.Quotient.mk K.1 x)) =
      Ideal.Quotient.mk H (Ideal.Quotient.mk K.1 x)
    rw [Ideal.Quotient.factor_mk]
    change quotientQuotientEquivComap K.1 H (Ideal.Quotient.mk J₀ x) = _
    unfold quotientQuotientEquivComap
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  have hSpec :
      (Scheme.Spec.mapIso E.toCommRingCatIso.op).hom ≫
          Spec.map (CommRingCat.ofHom qfac) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H)) := by
    change Spec.map (E.toCommRingCatIso.op.hom.unop) ≫
      Spec.map (CommRingCat.ofHom qfac) = _
    have h := congrArg
      (fun g : CommRingCat.of (A ⧸ K.1) ⟶
          CommRingCat.of ((A ⧸ K.1) ⧸ H) => Scheme.Spec.map g.op) hring
    simpa using h
  let eSpec : (BigAffineFppf.toScheme B S hS).obj V ≅
      Spec (.of (A ⧸ J₀)) := e₀ ≪≫ Scheme.Spec.mapIso E.toCommRingCatIso.op
  let e : (BigAffineFppf.toScheme B S hS).obj V ≅
      (BigAffineFppf.toScheme B S hS).obj (P.diagram.obj J) :=
    eSpec ≪≫ (P.quotientIso J).symm
  refine ⟨J, hJK, e, ?_⟩
  have htransition :
      (P.quotientIso J).inv ≫
          (BigAffineFppf.toScheme B S hS).map (P.diagram.map (homOfLE hJK)) =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom (homOfLE hJK)))) ≫
        (P.quotientIso K).inv := by
    rw [weak_quotient_transition_eq_spec_factor B S hS A X P (homOfLE hJK)]
    simp
  calc
    (BigAffineFppf.toScheme B S hS).map f = f' ≫ (P.quotientIso K).inv := by
      dsimp [f']
      simp [Category.assoc]
    _ = (e₀.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk H))) ≫
          (P.quotientIso K).inv := by
      rw [heq]
    _ = eSpec.hom ≫ Spec.map (CommRingCat.ofHom qfac) ≫
          (P.quotientIso K).inv := by
      dsimp [eSpec]
      rw [← hSpec]
      simp [Category.assoc]
    _ = e.hom ≫
          (BigAffineFppf.toScheme B S hS).map
            (P.diagram.map (homOfLE hJK)) := by
      change eSpec.hom ≫ Spec.map (CommRingCat.ofHom qfac) ≫
        (P.quotientIso K).inv =
        eSpec.hom ≫ (P.quotientIso J).inv ≫
          (BigAffineFppf.toScheme B S hS).map
            (P.diagram.map (homOfLE hJK))
      dsimp [qfac]
      exact (congrArg (fun g => eSpec.hom ≫ g) htransition).symm

private theorem exists_factor_to_weak_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (_hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)))
    (i : I) :
    ∃ (K : WeakIdeals A) (f : D.obj i ⟶ P.diagram.obj K),
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map f) ≫
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) K ≫ P.colimitIso.inv =
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) i ≫ eD.inv := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let e : X ≅ colimit
      (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙ F) := P.colimitIso
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  have hE : ∀ ⦃j k : WeakIdeals A⦄ (f : j ⟶ k),
      IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) :=
    fun _ _ f => weak_quotient_transition_closed_immersion B S hS A X P f
  obtain ⟨k, f, hf⟩ := exists_factor_to_stage_of_closedImmersion B S hS
    (WeakIdeals A) P.diagram hE X e (D.obj i)
    (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ eD.inv)
  exact ⟨k, f, hf⟩

/-- A morphism to a presented affine formal algebraic space from the sheaf represented by an
affine scheme of the site factors through one of the affine thickening stages of the
presentation, by a morphism of the big affine fppf category. -/
theorem exists_factor_to_affine_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (I : Type w₁) [Preorder I] [Small.{u + 1} I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)))
    (V : BigAffineFppf B S hS)
    (a : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj V) ⟶ X) :
    ∃ (j : I) (g : V ⟶ D.obj j),
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) j ≫ eD.inv = a := by
  exact exists_factor_to_stage_of_closedImmersion B S hS I D (fun _ _ f => (hD f).1) X eD V a

/-- Two morphisms of affine objects of the site are equal if their represented sheaves agree after
composing with a monomorphism. -/
private theorem eq_of_sheafifiedYoneda_map_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : BigAffineFppf B S hS} {Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (a b : U ⟶ V)
    (z : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Z) [Mono z]
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map a) ≫ z =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map b) ≫ z) :
    a = b := by
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
    Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)
  exact Functor.map_injective (F := BigAffineFppf.inclusion B S hS)
    (Functor.map_injective (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      ((cancel_mono z).1 h))

private theorem factor_map_isThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)))
    (i : I) (K : WeakIdeals A) (f : D.obj i ⟶ P.diagram.obj K)
    (hf : (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map f) ≫
      colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K ≫
      P.colimitIso.inv =
      colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫
      eD.inv) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map f) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigAffineFppf.inclusion B S hS
  let GD := D ⋙ T ⋙ F
  let GP := P.diagram ⋙ T ⋙ F
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  let U : BigFppfOver B S hS := T.obj (P.diagram.obj K)
  let a : F.obj U ⟶ X :=
    colimit.ι GP K ≫ P.colimitIso.inv
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS X I D hD eD
    (P.diagram.obj K) a
  obtain ⟨m, hui, hvj⟩ :=
    (inferInstance : IsDirected I (· ≤ ·)).directed i j
  let u := homOfLE hui
  let v := homOfLE hvj
  let g' : P.diagram.obj K ⟶ D.obj m := g ≫ D.map v
  have hcolv : F.map (T.map (D.map v)) ≫ colimit.ι GD m = colimit.ι GD j :=
    colimit.w (F := GD) v
  have hcolu : F.map (T.map (D.map u)) ≫ colimit.ι GD m = colimit.ι GD i :=
    colimit.w (F := GD) u
  have hgcol : F.map (T.map g') ≫ colimit.ι GD m =
      F.map (T.map g) ≫ colimit.ι GD j := by
    change F.map (T.map (g ≫ D.map v)) ≫ colimit.ι GD m = _
    simp only [Functor.map_comp, Category.assoc]
    rw [hcolv]
  have hcompD :
      F.map (T.map (f ≫ g')) ≫ colimit.ι GD m ≫ eD.inv =
        F.map (T.map (D.map u)) ≫ colimit.ι GD m ≫ eD.inv := by
    calc
      F.map (T.map (f ≫ g')) ≫ colimit.ι GD m ≫ eD.inv =
          F.map (T.map f) ≫ F.map (T.map g) ≫ colimit.ι GD j ≫ eD.inv := by
            simp only [Functor.map_comp]
            simpa [Category.assoc] using
              congrArg (fun z => F.map (T.map f) ≫ z ≫ eD.inv) hgcol
      _ = F.map (T.map f) ≫ colimit.ι GP K ≫ P.colimitIso.inv := by
            rw [hg]
      _ = colimit.ι GD i ≫ eD.inv := by rw [hf]
      _ = F.map (T.map (D.map u)) ≫ colimit.ι GD m ≫ eD.inv := by
            rw [← hcolu]
            simp [Category.assoc]
  have : Mono (colimit.ι GD m) :=
    mono_colimit_ι_of_closedImmersion B S hS I D (fun _ _ f => (hD f).1) m
  have hmapD : f ≫ g' = D.map u :=
    eq_of_sheafifiedYoneda_map_comp_eq B S hS _ _ (colimit.ι GD m ≫ eD.inv) hcompD
  obtain ⟨M, f', hf'⟩ := exists_factor_to_weak_stage B S hS A hA X P
    I D hD eD m
  obtain ⟨L, hKL, hML⟩ :=
    (inferInstance : IsDirected (WeakIdeals A) (· ≤ ·)).directed K M
  let tKL := homOfLE hKL
  let tML := homOfLE hML
  let q : P.diagram.obj K ⟶ P.diagram.obj L := P.diagram.map tKL
  let f'L : D.obj m ⟶ P.diagram.obj L := f' ≫ P.diagram.map tML
  have hg' : F.map (T.map g') ≫ colimit.ι GD m ≫ eD.inv =
      colimit.ι GP K ≫ P.colimitIso.inv := by
    change F.map (T.map g) ≫ colimit.ι GD j ≫ eD.inv =
      colimit.ι GP K ≫ P.colimitIso.inv at hg
    calc
      F.map (T.map g') ≫ colimit.ι GD m ≫ eD.inv =
          (F.map (T.map g') ≫ colimit.ι GD m) ≫ eD.inv := by
            simp [Category.assoc]
      _ = (F.map (T.map g) ≫ colimit.ι GD j) ≫ eD.inv :=
            congrArg (fun z => z ≫ eD.inv) hgcol
      _ = colimit.ι GP K ≫ P.colimitIso.inv := by
            simpa [a, GP, Category.assoc] using hg
  have hcolML : F.map (T.map (P.diagram.map tML)) ≫ colimit.ι GP L =
      colimit.ι GP M :=
    colimit.w (F := GP) tML
  have hcolKL : F.map (T.map q) ≫ colimit.ι GP L = colimit.ι GP K :=
    colimit.w (F := GP) tKL
  have hfL : F.map (T.map f'L) ≫ colimit.ι GP L =
      F.map (T.map f') ≫ colimit.ι GP M := by
    change F.map (T.map (f' ≫ P.diagram.map tML)) ≫ colimit.ι GP L = _
    simp only [Functor.map_comp, Category.assoc]
    rw [hcolML]
  have hcompP :
      F.map (T.map (g' ≫ f'L)) ≫ colimit.ι GP L ≫ P.colimitIso.inv =
        F.map (T.map q) ≫ colimit.ι GP L ≫ P.colimitIso.inv := by
    change F.map (T.map f') ≫ colimit.ι GP M ≫ P.colimitIso.inv =
        colimit.ι GD m ≫ eD.inv at hf'
    calc
      F.map (T.map (g' ≫ f'L)) ≫ colimit.ι GP L ≫ P.colimitIso.inv =
          F.map (T.map g') ≫ F.map (T.map f') ≫ colimit.ι GP M ≫ P.colimitIso.inv := by
            simp only [Functor.map_comp]
            simpa [Category.assoc] using
              congrArg (fun z => F.map (T.map g') ≫ z ≫ P.colimitIso.inv) hfL
      _ = F.map (T.map g') ≫ colimit.ι GD m ≫ eD.inv := by
            simpa [Category.assoc] using
              congrArg (fun z => F.map (T.map g') ≫ z) hf'
      _ = colimit.ι GP K ≫ P.colimitIso.inv := hg'
      _ = F.map (T.map q) ≫ colimit.ι GP L ≫ P.colimitIso.inv := by
            rw [← hcolKL]
            simp [Category.assoc]
  have : Mono (colimit.ι GP L) := weak_quotient_colimit_injection_mono B S hS A X P L
  have hmapP : g' ≫ f'L = q :=
    eq_of_sheafifiedYoneda_map_comp_eq B S hS _ _ (colimit.ι GP L ≫ P.colimitIso.inv) hcompP
  have hqclosed : IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map q) :=
    weak_quotient_transition_closed_immersion B S hS A X P tKL
  have hgclosed : IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map g') := by
    have : IsClosedImmersion
        ((BigAffineFppf.toScheme B S hS).map g' ≫
          (BigAffineFppf.toScheme B S hS).map f'L) := by
      rw [← Functor.map_comp, hmapP]
      exact hqclosed
    exact IsClosedImmersion.of_comp
      (f := (BigAffineFppf.toScheme B S hS).map g')
      (g := (BigAffineFppf.toScheme B S hS).map f'L)
  have hfgclosed : IsClosedImmersion
      ((BigAffineFppf.toScheme B S hS).map (f ≫ g')) := by
    rw [hmapD]
    exact (hD u).1
  have hfclosed : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map f) :=
    (IsClosedImmersion.comp_iff
      (f := (BigAffineFppf.toScheme B S hS).map f)
      (g := (BigAffineFppf.toScheme B S hS).map g')).mp hfgclosed
  have hfgsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map (f ≫ g')).base := by
    rw [hmapD]
    exact (hD u).2
  have hgsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map g').base :=
    Function.Surjective.of_comp (by simpa [Scheme.Hom.comp_base] using hfgsurj)
  have hginj : Function.Injective
      ((BigAffineFppf.toScheme B S hS).map g').base :=
    (Scheme.Hom.isClosedEmbedding _).injective
  have hfsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map f).base := by
    intro y
    obtain ⟨x, hx⟩ := hfgsurj (((BigAffineFppf.toScheme B S hS).map g').base y)
    refine ⟨x, ?_⟩
    apply hginj
    simpa [Scheme.Hom.comp_base] using hx
  exact ⟨hfclosed, hfsurj⟩

/-- An isomorphism of the underlying schemes of two objects of the big affine fppf site over `S`
that commutes with their structure morphisms to `S`, as an isomorphism in that site. -/
noncomputable def bigAffineIso_of_schemeIso_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U V : BigAffineFppf B S hS)
    (e : (BigAffineFppf.toScheme B S hS).obj U ≅
      (BigAffineFppf.toScheme B S hS).obj V)
    (hbase : e.hom ≫ B.inclusion.map
        ((BigAffineFppf.inclusion B S hS).obj V).hom =
      B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj U).hom) :
    U ≅ V := by
  let T := BigAffineFppf.inclusion B S hS
  let Uo := T.obj U
  let Vo := T.obj V
  letI : Functor.Full T := inferInstance
  letI : Functor.Faithful T := inferInstance
  have hbaseInv : e.inv ≫ B.inclusion.map Uo.hom = B.inclusion.map Vo.hom := by
    rw [← hbase, Iso.inv_hom_id_assoc]
  let leftMap := B.inclusion.preimage e.hom
  let rightMap := B.inclusion.preimage e.inv
  have hleft : leftMap ≫ Vo.hom = Uo.hom := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, B.inclusion.map_preimage]
  have hright : rightMap ≫ Uo.hom = Vo.hom := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, B.inclusion.map_preimage]
  let leftOver : Uo ⟶ Vo := Over.homMk leftMap hleft
  let rightOver : Vo ⟶ Uo := Over.homMk rightMap hright
  let a := T.preimage leftOver
  let b := T.preimage rightOver
  have ha := T.map_preimage leftOver
  have hb := T.map_preimage rightOver
  have hleftRight : leftMap ≫ rightMap = 𝟙 Uo.left := by
    change B.inclusion.preimage e.hom ≫ B.inclusion.preimage e.inv = _
    rw [← B.inclusion.preimage_comp, e.hom_inv_id]
    exact B.inclusion.preimage_id
  have hrightLeft : rightMap ≫ leftMap = 𝟙 Vo.left := by
    change B.inclusion.preimage e.inv ≫ B.inclusion.preimage e.hom = _
    rw [← B.inclusion.preimage_comp, e.inv_hom_id]
    exact B.inclusion.preimage_id
  refine ⟨a, b, ?_, ?_⟩
  · apply T.map_injective
    apply Over.OverMorphism.ext
    change (T.map a).left ≫ (T.map b).left = 𝟙 _
    rw [ha, hb]
    exact hleftRight
  · apply T.map_injective
    apply Over.OverMorphism.ext
    change (T.map b).left ≫ (T.map a).left = 𝟙 _
    rw [ha, hb]
    exact hrightLeft

private theorem weak_stage_map_of_colimit_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    [Nonempty (WeakIdeals A)] [IsDirected (WeakIdeals A) (· ≤ ·)]
    {J K : WeakIdeals A} (g : P.diagram.obj J ⟶ P.diagram.obj K)
    (hcol : (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map g) ≫
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K =
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) J) :
    ∃ h : J ≤ K, g = P.diagram.map (homOfLE h) := by
  classical
  let T := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let GP := P.diagram ⋙ T ⋙ F
  obtain ⟨L, hJL, hKL⟩ := (inferInstance : IsDirected (WeakIdeals A) (· ≤ ·)).directed J K
  let tJL := P.diagram.map (homOfLE hJL)
  let tKL := P.diagram.map (homOfLE hKL)
  have hcolL : F.map (T.map (g ≫ tKL)) ≫ colimit.ι GP L =
      F.map (T.map tJL) ≫ colimit.ι GP L := by
    have hwKL := colimit.w (F := GP) (homOfLE hKL)
    have hwJL := colimit.w (F := GP) (homOfLE hJL)
    change F.map (T.map tKL) ≫ colimit.ι GP L = _ at hwKL
    change F.map (T.map tJL) ≫ colimit.ι GP L = _ at hwJL
    calc
      F.map (T.map (g ≫ tKL)) ≫ colimit.ι GP L =
          F.map (T.map g) ≫ colimit.ι GP K := by
            simp only [Functor.map_comp, Category.assoc]
            rw [hwKL]
      _ = colimit.ι GP J := hcol
      _ = F.map (T.map tJL) ≫ colimit.ι GP L := hwJL.symm
  have : Mono (colimit.ι GP L) := weak_quotient_colimit_injection_mono
    B S hS A X P L
  have hcat : g ≫ tKL = tJL := eq_of_sheafifiedYoneda_map_comp_eq B S hS _ _ _ hcolL
  let qJ := P.quotientIso J
  let qK := P.quotientIso K
  let qL := P.quotientIso L
  let toSch := BigAffineFppf.toScheme B S hS
  let fKL : A ⧸ L.1 →+* A ⧸ K.1 :=
    Ideal.Quotient.factor (show L.1 ≤ K.1 from leOfHom (homOfLE hKL))
  let fJL : A ⧸ L.1 →+* A ⧸ J.1 :=
    Ideal.Quotient.factor (show L.1 ≤ J.1 from leOfHom (homOfLE hJL))
  let coord : (Spec (.of (A ⧸ J.1))) ⟶ Spec (.of (A ⧸ K.1)) :=
    qJ.inv ≫ toSch.map g ≫ qK.hom
  let coordOp := Spec.fullyFaithful.preimage coord
  have hcoord : coordOp ≫ (CommRingCat.ofHom fKL).op =
      (CommRingCat.ofHom fJL).op := by
    apply Scheme.Spec.map_injective
    have hnKL := P.quotientIso_natural (homOfLE hKL)
    have hnJL := P.quotientIso_natural (homOfLE hJL)
    calc
      Scheme.Spec.map (coordOp ≫ (CommRingCat.ofHom fKL).op) =
          coord ≫ Scheme.Spec.map (CommRingCat.ofHom fKL).op := by
            simp [coord, coordOp]
      _ = qJ.inv ≫ toSch.map (g ≫ tKL) ≫ qL.hom := by
            dsimp [coord]
            rw [Functor.map_comp]
            simp only [Category.assoc]
            rw [hnKL]
      _ = qJ.inv ≫ toSch.map tJL ≫ qL.hom := by
            rw [hcat]
      _ = Scheme.Spec.map (CommRingCat.ofHom fJL).op := by
            dsimp [tJL, fJL]
            rw [hnJL]
            simp
  have hcoordRing : coordOp.unop.hom.comp fKL = fJL := by
    have h := congrArg Quiver.Hom.unop hcoord
    simp only [unop_comp, Quiver.Hom.unop_op] at h
    have h' := congrArg CommRingCat.Hom.hom h
    simpa using h'
  have hcontain : K.1 ≤ J.1 := by
    intro x hx
    have hval := congrArg
      (fun ψ : A ⧸ L.1 →+* A ⧸ J.1 => ψ (Ideal.Quotient.mk L.1 x)) hcoordRing
    change coordOp.unop.hom (fKL (Ideal.Quotient.mk L.1 x)) =
      fJL (Ideal.Quotient.mk L.1 x) at hval
    have hleft : fKL (Ideal.Quotient.mk L.1 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [hleft, map_zero] at hval
    have hright : fJL (Ideal.Quotient.mk L.1 x) = Ideal.Quotient.mk J.1 x := by
      simp [fJL, Ideal.Quotient.factor_mk]
    rw [hright] at hval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hval.symm
  let hJK : J ≤ K := hcontain
  let tJK := P.diagram.map (homOfLE hJK)
  let fJK : A ⧸ K.1 →+* A ⧸ J.1 :=
    Ideal.Quotient.factor (show K.1 ≤ J.1 from leOfHom (homOfLE hJK))
  have hfactorComp : (CommRingCat.ofHom fJK).op ≫ (CommRingCat.ofHom fKL).op =
      (CommRingCat.ofHom fJL).op := by
    apply Quiver.Hom.unop_inj
    apply CommRingCat.hom_ext
    ext x
    simp [fJK, fKL, fJL]
  have hspec : coord ≫ Scheme.Spec.map (CommRingCat.ofHom fKL).op =
      Scheme.Spec.map (CommRingCat.ofHom fJK).op ≫
        Scheme.Spec.map (CommRingCat.ofHom fKL).op := by
    calc
      coord ≫ Scheme.Spec.map (CommRingCat.ofHom fKL).op =
          Scheme.Spec.map (CommRingCat.ofHom fJL).op := by
            have h := congrArg Scheme.Spec.map hcoord
            have hmapcoord : Scheme.Spec.map coordOp = coord :=
              Spec.fullyFaithful.map_preimage coord
            simpa only [Functor.map_comp, hmapcoord] using h
      _ = Scheme.Spec.map
          ((CommRingCat.ofHom fJK).op ≫ (CommRingCat.ofHom fKL).op) := by
            rw [hfactorComp]
      _ = Scheme.Spec.map (CommRingCat.ofHom fJK).op ≫
          Scheme.Spec.map (CommRingCat.ofHom fKL).op := by
            rw [Functor.map_comp]
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom fKL).op) := by
    have hsurj : Function.Surjective fKL := by
      dsimp [fKL]
      exact Ideal.Quotient.factor_surjective _
    have : IsClosedImmersion (Scheme.Spec.map (CommRingCat.ofHom fKL).op) :=
      IsClosedImmersion.spec_of_surjective _ hsurj
    infer_instance
  have hcoord_eq : coord = Scheme.Spec.map (CommRingCat.ofHom fJK).op :=
    (cancel_mono _).1 hspec
  have hcoord_t : qJ.inv ≫ toSch.map tJK ≫ qK.hom =
      Scheme.Spec.map (CommRingCat.ofHom fJK).op := by
    dsimp [tJK, fJK]
    rw [weak_quotient_transition_eq_spec_factor B S hS A X P (homOfLE hJK)]
    simp [qJ, qK]
  have hscheme : toSch.map g = toSch.map tJK := by
    apply (cancel_epi qJ.inv).1
    apply (cancel_mono qK.hom).1
    simpa [coord] using hcoord_eq.trans hcoord_t.symm
  refine ⟨hJK, ?_⟩
  exact Functor.map_injective (F := toSch) hscheme

/-- Every affine thickening presentation of a formal spectrum comes from a
cofinal system of weak ideals of definition. The stage identifications are
compatible with the canonical quotient transition morphisms. -/
public theorem presentation_quotients_cofinal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ (J : I → WeakIdeals A) (e : ∀ i, D.obj i ≅ P.diagram.obj (J i)),
      (∀ ⦃i j : I⦄ (f : i ⟶ j),
        ∃ h : J i ≤ J j,
          D.map f ≫ (e j).hom =
            (e i).hom ≫ P.diagram.map (homOfLE h)) ∧
      (∀ i : I,
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map (e i).hom) ≫
          colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (J i) ≫
          P.colimitIso.inv =
        colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫
          eD.inv) ∧
      (∀ K : WeakIdeals A, ∃ i : I, K ≤ J i) := by
  classical
  have : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  choose K f hf using fun i => exists_factor_to_weak_stage B S hS A hA X P I D hD eD i
  choose J hJK eScheme hfactor using fun i =>
    exists_weakIdeal_over_thickening_stage B S hS A X P (K i) (f i)
      (factor_map_isThickening B S hS A hA X P I D hD eD i (K i) (f i) (hf i))
  have hbase (i : I) : (eScheme i).hom ≫ B.inclusion.map
      ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj (J i))).hom =
      B.inclusion.map
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)).hom := by
    rw [← toScheme_map_comp_structure B S hS (f i),
      ← toScheme_map_comp_structure B S hS (P.diagram.map (homOfLE (hJK i))), ← Category.assoc,
      hfactor]
  let e (i : I) : D.obj i ≅ P.diagram.obj (J i) :=
    bigAffineIso_of_schemeIso_over B S hS (D.obj i) (P.diagram.obj (J i))
      (eScheme i) (hbase i)
  have htransitionColimit (i : I) :
      (Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (P.diagram.map (homOfLE (hJK i)))) ≫
        colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)) (K i) =
      colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)) (J i) := by
    change (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda
        (BigFppfOver.topology B S hS)).map
          (homOfLE (hJK i)) ≫ _ = _
    exact colimit.w (F := P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (homOfLE (hJK i))
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let GP := P.diagram ⋙ T ⋙ F
  let GD := D ⋙ T ⋙ F
  have hcanonical (i : I) :
      F.map (T.map (e i).hom) ≫ colimit.ι GP (J i) ≫ P.colimitIso.inv =
        colimit.ι GD i ≫ eD.inv := by
    have hehom : (BigAffineFppf.toScheme B S hS).map (e i).hom =
        (eScheme i).hom := by
      change B.inclusion.map
        (Over.Hom.left (T.map (T.preimage
          (Over.homMk (B.inclusion.preimage (eScheme i).hom) _)))) = _
      rw [T.map_preimage]
      change B.inclusion.map (B.inclusion.preimage (eScheme i).hom) = _
      exact B.inclusion.map_preimage (eScheme i).hom
    have hfactorCat : f i = (e i).hom ≫ P.diagram.map (homOfLE (hJK i)) := by
      apply (Functor.map_injective
        (F := BigAffineFppf.toScheme B S hS))
      rw [Functor.map_comp, hehom]
      exact hfactor i
    calc
      F.map (T.map (e i).hom) ≫ colimit.ι GP (J i) ≫ P.colimitIso.inv =
          F.map (T.map (e i).hom) ≫
            (F.map (T.map (P.diagram.map (homOfLE (hJK i)))) ≫
              colimit.ι GP (K i)) ≫ P.colimitIso.inv := by
                rw [htransitionColimit]
      _ = F.map (T.map (f i)) ≫ colimit.ι GP (K i) ≫ P.colimitIso.inv := by
            simp only [hfactorCat, Functor.map_comp, Category.assoc]
      _ = colimit.ι GD i ≫ eD.inv := hf i
  refine ⟨J, e, ?_, hcanonical, ?_⟩
  · intro i j f
    let g : P.diagram.obj (J i) ⟶ P.diagram.obj (J j) :=
      (e i).inv ≫ D.map f ≫ (e j).hom
    have hcolIso : F.map (T.map g) ≫ colimit.ι GP (J j) ≫ P.colimitIso.inv =
        colimit.ι GP (J i) ≫ P.colimitIso.inv := by
      calc
        F.map (T.map g) ≫ colimit.ι GP (J j) ≫ P.colimitIso.inv =
            F.map (T.map (e i).inv) ≫ F.map (T.map (D.map f)) ≫
              (F.map (T.map (e j).hom) ≫ colimit.ι GP (J j) ≫ P.colimitIso.inv) := by
                simp [g, Category.assoc]
        _ = F.map (T.map (e i).inv) ≫ F.map (T.map (D.map f)) ≫
              (colimit.ι GD j ≫ eD.inv) := by rw [hcanonical j]
        _ = F.map (T.map (e i).inv) ≫ colimit.ι GD i ≫ eD.inv := by
              have hcolD : F.map (T.map (D.map f)) ≫ colimit.ι GD j =
                  colimit.ι GD i := colimit.w (F := GD) f
              simp only [← hcolD, Category.assoc]
        _ = F.map (T.map (e i).inv) ≫
              (F.map (T.map (e i).hom) ≫ colimit.ι GP (J i) ≫ P.colimitIso.inv) := by
                rw [hcanonical i]
        _ = colimit.ι GP (J i) ≫ P.colimitIso.inv := by simp
    rw [← Category.assoc] at hcolIso
    obtain ⟨h, hg⟩ := weak_stage_map_of_colimit_eq B S hS A X P g
      ((cancel_mono P.colimitIso.inv).1 hcolIso)
    refine ⟨h, ?_⟩
    calc
      D.map f ≫ (e j).hom = (e i).hom ≫ g := by simp [g]
      _ = (e i).hom ≫ P.diagram.map (homOfLE h) := by rw [hg]
  · intro K₀
    let a : F.obj (T.obj (P.diagram.obj K₀)) ⟶ X :=
      colimit.ι GP K₀ ≫ P.colimitIso.inv
    obtain ⟨i, g, hg⟩ := exists_factor_to_affine_stage B S hS X I D hD eD
      (P.diagram.obj K₀) a
    let m : P.diagram.obj K₀ ⟶ P.diagram.obj (J i) := g ≫ (e i).hom
    have hcolIso : F.map (T.map m) ≫ colimit.ι GP (J i) ≫ P.colimitIso.inv =
        colimit.ι GP K₀ ≫ P.colimitIso.inv := by
      calc
        F.map (T.map m) ≫ colimit.ι GP (J i) ≫ P.colimitIso.inv =
            F.map (T.map g) ≫ colimit.ι GD i ≫ eD.inv := by
              simp [m, Category.assoc, hcanonical i]
        _ = colimit.ι GP K₀ ≫ P.colimitIso.inv := hg
    rw [← Category.assoc] at hcolIso
    obtain ⟨h, _⟩ := weak_stage_map_of_colimit_eq B S hS A X P m
      ((cancel_mono P.colimitIso.inv).1 hcolIso)
    exact ⟨i, h⟩


/-! ### Condition (1) of Stacks 0AIC implies condition (5) -/

/-- Passing to a smaller quotient by a weak ideal of definition is surjective on spectra: every
element of the larger ideal is topologically nilpotent, hence nilpotent modulo the smaller
(open) one, so the kernel of the comparison map lies in the nilradical. -/
private theorem surjective_spec_quotient_factor
    {A : Type u} [CommRing A] [TopologicalSpace A] {J K : Ideal A}
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) (hK : IsOpen (K : Set A))
    (h : K ≤ J) :
    Function.Surjective
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))) := by
  have hker : (RingHom.ker (Ideal.Quotient.factor h) : Set (A ⧸ K)) ⊆ nilradical (A ⧸ K) := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk] at hy
    have hxJ : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨n, hn⟩ :=
      (hJ.2 x hxJ).exists_pow_mem_of_mem_nhds (hK.mem_nhds K.zero_mem)
    refine ⟨n + 1, ?_⟩
    rw [← map_pow]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    simpa [pow_succ] using K.mul_mem_right x hn
  have key : Function.Surjective
      (PrimeSpectrum.comap (Ideal.Quotient.factor h)) := by
    rw [← Set.range_eq_univ,
      range_comap_of_surjective (A ⧸ J) (Ideal.Quotient.factor h)
        (Ideal.Quotient.factor_surjective h),
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    exact hker
  exact key

/-- Each transition morphism of the canonical weak-ideal presentation is a thickening: it is a
closed immersion, and surjective because the larger weak ideal of definition becomes nilpotent
modulo the smaller one. -/
@[ega "I 10.7.4" "special case"]
theorem weak_quotient_transition_isThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (P : WeakIdealColimitPresentation B S hS A X)
    {J K : WeakIdeals A} (f : J ⟶ K) :
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (P.diagram.map f)) := by
  refine ⟨weak_quotient_transition_closed_immersion B S hS A X P f, ?_⟩
  have hle : (K.1 : Ideal A) ≤ J.1 := leOfHom f
  let qSpec : Spec (.of (A ⧸ J.1)) ⟶ Spec (.of (A ⧸ K.1)) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))
  have hq : Function.Surjective qSpec :=
    surjective_spec_quotient_factor J.2 K.2.1 hle
  have hiso₁ : Function.Surjective (P.quotientIso J).hom.base :=
    (ConcreteCategory.bijective_of_isIso (P.quotientIso J).hom.base).2
  have hiso₂ : Function.Surjective (P.quotientIso K).inv.base :=
    (ConcreteCategory.bijective_of_isIso (P.quotientIso K).inv.base).2
  rw [weak_quotient_transition_eq_spec_factor B S hS A X P f]
  change Function.Surjective
    (((P.quotientIso J).hom ≫ qSpec ≫ (P.quotientIso K).inv)).base
  rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base]
  exact (hiso₂.comp hq).comp hiso₁

/-- The universe lift of the index of weak ideals of definition, as an equivalence of
categories. A presentation in `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace` is
indexed by a type one universe above the schemes, whereas the weak ideals of definition of a
ring in `Type u` form a `Type u`. -/
private def weakIdealsULiftEquivalence (A : Type u) [CommRing A] [TopologicalSpace A] :
    ULift.{u + 1} (WeakIdeals A) ≌ WeakIdeals A where
  functor :=
    { obj := ULift.down
      map := fun f ↦ homOfLE (ULift.down_le.mpr (leOfHom f))
      map_id := fun _ ↦ Subsingleton.elim _ _
      map_comp := fun _ _ ↦ Subsingleton.elim _ _ }
  inverse :=
    { obj := ULift.up
      map := fun f ↦ homOfLE (ULift.down_le.mp (leOfHom f))
      map_id := fun _ ↦ Subsingleton.elim _ _
      map_comp := fun _ _ ↦ Subsingleton.elim _ _ }
  unitIso := NatIso.ofComponents (fun i ↦ Iso.refl i) (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun i ↦ Iso.refl i) (fun _ ↦ Subsingleton.elim _ _)
  functor_unitIso_comp := fun _ ↦ Subsingleton.elim _ _

/-- **Stacks 0AIC, (1) ⇒ "`X` has a presentation by affine thickenings".** The canonical
presentation of the formal spectrum of a weakly admissible topological ring by the spectra of
its quotients by weak ideals of definition is a presentation by affine thickenings over a
nonempty directed index: the weak ideals of definition of a weakly admissible ring are nonempty
and closed under intersection, and the transition morphisms are thickenings because an element
of a weak ideal of definition is topologically nilpotent, hence nilpotent modulo any smaller —
and therefore open — one.

Nothing here bounds the size of the site. The set-theoretic condition of Stacks 0AIS, the other
half of being an affine formal algebraic space, does: it asks the site to contain a single object
surjecting onto `X`, which for this presentation is the coproduct of all the quotient spectra. -/
theorem hasThickeningPresentation_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) :
    HasThickeningPresentation B S hS X := by
  have hne : Nonempty (WeakIdeals A) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hA.1
  have hdir : IsDirected (WeakIdeals A) (· ≤ ·) :=
    TopologicalRing.isDirected_weakIdealOfDefinitionIndex A
  refine ⟨ULift.{u + 1} (WeakIdeals A), inferInstance, ⟨ULift.up hne.some⟩, ?_, ?_⟩
  · refine ⟨fun i j ↦ ?_⟩
    obtain ⟨k, hik, hjk⟩ := hdir.directed i.down j.down
    exact ⟨ULift.up k, hik, hjk⟩
  · refine ⟨(weakIdealsULiftEquivalence A).functor ⋙ P.diagram, ?_, ?_⟩
    · intro i j f
      exact weak_quotient_transition_isThickening B S hS A X P _
    · exact ⟨P.colimitIso ≪≫
        (HasColimit.isoOfEquivalence (weakIdealsULiftEquivalence A) (Iso.refl _)).symm⟩

/-- **Stacks 0AIC, (1) ⇒ "`X` is an affine formal algebraic space".** The canonical presentation
of the formal spectrum of a weakly admissible topological ring by the spectra of its quotients
by weak ideals of definition is a presentation by affine thickenings over a nonempty directed
index, so an fppf sheaf carrying such a presentation and satisfying the set-theoretic condition
of Stacks 0AIS is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) :
    IsAffineFormalAlgebraicSpace B S hS X :=
  ⟨hX, hasThickeningPresentation_of_weakIdealColimitPresentation B S hS A hA P⟩

/-- **The stage rings of an arbitrary presentation of a formal spectrum are the quotients of the
presenting ring.** If `X` is the colimit of the spectra of the quotients of a weakly admissible
topological ring `A` by its weak ideals of definition, then any presentation `X = colim Xᵢ` by
affine thickenings carries weak ideals of definition `Jᵢ` with
`Γ(Xᵢ, 𝒪) ≅ A ⧸ Jᵢ`, compatibly with all transition morphisms, and the `Jᵢ` are cofinal among
the weak ideals of definition of `A`.

This is the ring-theoretic form of
`AlgebraicGeometry.FormalSpace.presentation_quotients_cofinal`: that lemma identifies the stages
with the quotient *spectra*, and taking global sections turns the identification into one of the
stage rings with the quotients themselves. -/
public theorem exists_stageQuotientIso_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ (J : I → WeakIdeals A)
      (χ : ∀ k : I, CommRingCat.of (A ⧸ (J k).1) ≅
        Scheme.Γ.obj (Opposite.op ((BigAffineFppf.toScheme B S hS).obj (D.obj k)))),
      (∀ (k l : I) (f : k ⟶ l) (a : A),
        Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (D.map f)).op
            ((χ l).hom (Ideal.Quotient.mk (J l).1 a)) =
          (χ k).hom (Ideal.Quotient.mk (J k).1 a)) ∧
      (∀ K : WeakIdeals A, ∃ i : I, K ≤ J i) := by
  classical
  obtain ⟨J, e, hnat, -, hcof⟩ := presentation_quotients_cofinal B S hS A hA X P I D hD eD
  let toSch := BigAffineFppf.toScheme B S hS
  let α : ∀ k : I, toSch.obj (D.obj k) ≅ Spec (CommRingCat.of (A ⧸ (J k).1)) :=
    fun k ↦ toSch.mapIso (e k) ≪≫ P.quotientIso (J k)
  let χ : ∀ k : I, CommRingCat.of (A ⧸ (J k).1) ≅
      Scheme.Γ.obj (Opposite.op (toSch.obj (D.obj k))) :=
    fun k ↦ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J k).1))).symm ≪≫
      Scheme.Γ.mapIso (α k).op
  have hcompat : ∀ (k l : I) (f : k ⟶ l) (a : A),
      Scheme.Γ.map ((toSch.map (D.map f)).op) ((χ l).hom (Ideal.Quotient.mk (J l).1 a)) =
        (χ k).hom (Ideal.Quotient.mk (J k).1 a) := by
    intro k l f a
    obtain ⟨h, he⟩ := hnat f
    let φ : CommRingCat.of (A ⧸ (J l).1) ⟶ CommRingCat.of (A ⧸ (J k).1) :=
      CommRingCat.ofHom (Ideal.Quotient.factor (show (J l).1 ≤ (J k).1 from h))
    have hsq : toSch.map (D.map f) ≫ (α l).hom = (α k).hom ≫ Spec.map φ := by
      have hq := P.quotientIso_natural (homOfLE h)
      simp only [α, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc, hq]
    have hfun : Scheme.Γ.map ((α l).hom.op) ≫ Scheme.Γ.map ((toSch.map (D.map f)).op) =
        Scheme.Γ.map ((Spec.map φ).op) ≫ Scheme.Γ.map ((α k).hom.op) := by
      rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp]
      exact congrArg (fun g ↦ Scheme.Γ.map (Quiver.Hom.op g)) hsq
    have hnat2 : φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J k).1))).inv =
        (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫
          Scheme.Γ.map ((Spec.map φ).op) :=
      (Scheme.ΓSpecIso_inv_naturality φ).trans
        (congrArg (fun m ↦ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫ m)
          (Scheme.Γ_map_op (Spec.map φ)).symm)
    have hcomp : (χ l).hom ≫ Scheme.Γ.map ((toSch.map (D.map f)).op) = φ ≫ (χ k).hom :=
      calc (χ l).hom ≫ Scheme.Γ.map ((toSch.map (D.map f)).op)
          = (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫
              Scheme.Γ.map ((α l).hom.op) ≫
                Scheme.Γ.map ((toSch.map (D.map f)).op) :=
            Category.assoc _ _ _
        _ = (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫
              Scheme.Γ.map ((Spec.map φ).op) ≫ Scheme.Γ.map ((α k).hom.op) :=
            congrArg (fun m ↦ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫ m) hfun
        _ = ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J l).1))).inv ≫
              Scheme.Γ.map ((Spec.map φ).op)) ≫ Scheme.Γ.map ((α k).hom.op) :=
            (Category.assoc _ _ _).symm
        _ = (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ (J k).1))).inv) ≫
              Scheme.Γ.map ((α k).hom.op) :=
            congrArg (fun m ↦ m ≫ Scheme.Γ.map ((α k).hom.op)) hnat2.symm
        _ = φ ≫ (χ k).hom := Category.assoc _ _ _
    have hap : Scheme.Γ.map ((toSch.map (D.map f)).op)
          ((χ l).hom (Ideal.Quotient.mk (J l).1 a)) =
        (χ k).hom (φ (Ideal.Quotient.mk (J l).1 a)) :=
      congrArg (fun m : CommRingCat.of (A ⧸ (J l).1) ⟶
          Scheme.Γ.obj (Opposite.op (toSch.obj (D.obj k))) ↦
        m (Ideal.Quotient.mk (J l).1 a)) hcomp
    have hφ : φ (Ideal.Quotient.mk (J l).1 a) = Ideal.Quotient.mk (J k).1 a :=
      Ideal.Quotient.factor_mk (show (J l).1 ≤ (J k).1 from h) a
    exact hap.trans (congrArg (fun y ↦ (χ k).hom y) hφ)
  exact ⟨J, χ, hcompat, hcof⟩

/-- **Stacks 0AIC, (1) ⇒ (5), the surjectivity.** If `X` is the colimit of the spectra of the
quotients of a weakly admissible topological ring `A` by its weak ideals of definition, then the
section-ring projections of *every* presentation of `X` by affine thickenings are surjective.
By `AlgebraicGeometry.FormalSpace.presentation_quotients_cofinal` each stage of such a
presentation is the spectrum of a quotient `A ⧸ Jᵢ`, compatibly with the transition morphisms,
so the compatible family of the classes of a single element of `A` lifts any prescribed section
of a single stage. -/
theorem hasSurjectiveSectionProjections_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (eD : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    HasSurjectiveSectionProjections B S hS D := by
  classical
  obtain ⟨J, χ, hcompat, -⟩ :=
    exists_stageQuotientIso_of_weakIdealColimitPresentation B S hS A hA P I D hD eD
  intro i t
  obtain ⟨a, ha⟩ : ∃ a : A, (χ i).hom (Ideal.Quotient.mk (J i).1 a) = t := by
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((χ i).inv t)
    exact ⟨w, by rw [hw]; exact (χ i).inv_hom_id_apply t⟩
  exact ⟨⟨fun k ↦ (χ k.unop).hom (Ideal.Quotient.mk (J k.unop).1 a),
    fun {k l} g ↦ hcompat l.unop k.unop g.unop a⟩, ha⟩

/-- **Stacks 0AIC, (1) ⇒ (5)**, with condition (1) taken apart. An fppf sheaf satisfying the
set-theoretic condition of Stacks 0AIS which is the colimit of the spectra of the quotients of a
weakly admissible topological ring by its weak ideals of definition is an affine formal
algebraic space all of whose presentations by affine thickenings have surjective section-ring
projections. -/
theorem hasAllSurjectivePresentations_of_weakIdealColimitPresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) :
    HasAllSurjectivePresentations B S hS X := by
  refine ⟨isAffineFormalAlgebraicSpace_of_weakIdealColimitPresentation B S hS A hA hX P, ?_⟩
  intro I pre hne hdir D hD hcolim
  obtain ⟨eD⟩ := hcolim
  exact hasSurjectiveSectionProjections_of_weakIdealColimitPresentation B S hS A hA P I D hD eD

/-- **Stacks 0AIC, (1) ⇒ (5).** Condition (1) of Stacks 0AIC — the existence of a weakly
admissible topological ring over `S` presenting `X` as the colimit of the spectra of its
quotients by weak ideals of definition — implies condition (5): `X` is an affine formal
algebraic space and *every* presentation of it by affine thickenings has surjective section-ring
projections. -/
@[stacks 0AIC "(1) implies (5)"]
theorem hasAllSurjectivePresentations_of_exists_weaklyAdmissible
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X)
    (h : ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : IsTopologicalRing A) (_ : IsLinearTopology A A),
      letI : CommRing A := ‹CommRing A›
      letI : TopologicalSpace A := ‹TopologicalSpace A›
      letI : IsTopologicalRing A := ‹IsTopologicalRing A›
      letI : IsLinearTopology A A := ‹IsLinearTopology A A›
      TopologicalRing.IsWeaklyAdmissible A ∧
        Nonempty (WeakIdealColimitPresentation B S hS A X)) :
    HasAllSurjectivePresentations B S hS X := by
  obtain ⟨A, instCR, instTS, instTR, instLT, hA, ⟨P⟩⟩ := h
  let : CommRing A := instCR
  let : TopologicalSpace A := instTS
  let : IsTopologicalRing A := instTR
  let : IsLinearTopology A A := instLT
  exact hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS A hA hX P

end AlgebraicGeometry.FormalSpace

end
