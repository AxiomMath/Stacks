module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import StacksCore.CategoryTheory.Sites.Representable.MapsFromRepresentable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact

/-!
# Factoring a map from a quasi-compact algebraic space through a thickening stage

Let an fppf sheaf over `S` be presented as a directed colimit of sheaves represented by affine
schemes whose transition morphisms are closed immersions -- in particular, let an affine formal
algebraic space be presented as Stacks 0AI7 presents it. Then every morphism to it from a
quasi-compact algebraic space over `S` factors through one of the stages of the presentation.

## Main results

* `AlgebraicGeometry.exists_factor_through_thickening`: the factorization through a stage of
  a specified presentation, asking of the presentation only that its transition morphisms be
  closed immersions and of the target nothing else at all.

## Implementation notes

The presentation and the isomorphism identifying the sheaf with the colimit are part of the
data, so the factorization is an equality with the canonical colimit injection rather than a
statement up to isomorphism. Being an affine formal algebraic space is then not needed as a
hypothesis: the presentation along thickenings is the whole input, so the statement also
applies to a sheaf presented that way which is not known to satisfy the set-theoretic
condition of Stacks 0AIS.

An algebraic space is a sheaf of sets in `Type u`, whereas the colimit sheaf lives in
`Type (u + 1)`; a morphism from the former to the latter is expressed as a morphism out of
the sheafification of the universe-lifted presheaf.

Two ingredients carry the argument. The quasi-compact atlas of the algebraic space makes the
representing object of the site quasi-compact, so a section of a filtered colimit of sheaves
over it comes from a single stage. The transition morphisms of the presentation are closed
immersions, hence monomorphisms of represented sheaves, which makes each colimit injection a
monomorphism; the chosen stage is then reached by lifting the strong epimorphism from the
atlas against that monomorphism.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w w₁ w₂

namespace AlgebraicGeometry

/-- Factorization through a stage of a presentation whose transition morphisms are closed
immersions, the shared argument for the two versions below. -/
private theorem exists_factor_through_thickening_aux
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type w₁) [Preorder I] [Small.{u + 1} I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
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
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) q).presheaf
      (𝟙 (yoneda.obj U)) := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, fun A V g fst snd hpb => ?_⟩
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    show Etale (q.map snd)
    infer_instance
  have hloc := _root_.AlgebraicGeometry.isLocallySurjective_of_surjective_etale B S hS a hasurj
    (hYEtale U (𝟙 (yoneda.obj U)) hid)
  let aLift := Functor.whiskerRight a uliftFunctor.{u + 1, u}
  have hlocLift : Presheaf.IsLocallySurjective J aLift := ⟨fun s => by
    refine J.superset_covering ?_ (hloc.imageSieve_mem s.down)
    rintro V' g' ⟨x, hx⟩
    exact ⟨⟨x⟩, congrArg ULift.up hx⟩⟩
  let p : (Sheaf.sheafifiedYoneda J).obj U ⟶
      (presheafToSheaf J (Type (u + 1))).obj (Y ⋙ uliftFunctor.{u + 1, u}) :=
    (presheafToSheaf J (Type (u + 1))).map aLift
  have hp : Epi p := (Sheaf.isLocallySurjective_iff_epi p).1
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff J aLift).2 hlocLift)
  let F := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  have htrans : ∀ i j (g : i ⟶ j), Mono (F.map g) := fun _ _ g => by
    show Mono ((Sheaf.sheafifiedYoneda J).map
      ((BigAffineFppf.inclusion B S hS).map (D.map g)))
    have : IsClosedImmersion (q.map ((BigAffineFppf.inclusion B S hS).map (D.map g))) := hD g
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying J q _ inferInstance
  let G := (sheafSections J (Type (u + 1))).obj (op U)
  let α : (Sheaf.sheafifiedYoneda J).obj U ⟶ colimit F := p ≫ f ≫ e.hom
  have hbij : Function.Bijective (colimit.post F G) :=
    (Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.1
      (AlgebraicGeometry.FormalSpace.isQuasiCompactObject_over_of_compact_scheme B S hS U) htrans
  obtain ⟨z, hz⟩ := hbij.2 ((Sheaf.sectionEquiv J) α)
  let Fsec := F ⋙ G
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep Fsec (colimit.isColimit Fsec) z
  let gi : (Sheaf.sheafifiedYoneda J).obj U ⟶ F.obj i := (Sheaf.sectionEquiv J).symm x
  have hgi : gi ≫ colimit.ι F i = α := by
    apply (Sheaf.sectionEquiv J).injective
    calc
      (Sheaf.sectionEquiv J) (gi ≫ colimit.ι F i) = (colimit.ι F i).hom.app (op U) x := by
        rw [Sheaf.sectionEquiv_comp]
        show (colimit.ι F i).hom.app (op U)
          ((Sheaf.sectionEquiv J) ((Sheaf.sectionEquiv J).symm x)) = _
        exact congrArg ((colimit.ι F i).hom.app (op U))
          ((Sheaf.sectionEquiv J).apply_symm_apply x)
      _ = colimit.post F G (colimit.ι Fsec i x) :=
        (ConcreteCategory.congr_hom (colimit.ι_post F G i) x).symm
      _ = colimit.post F G z := congrArg (colimit.post F G) hx
      _ = (Sheaf.sectionEquiv J) α := hz
  have : Mono (colimit.ι F i) := Sheaf.mono_colimit_ι_of_mono_transition F htrans i
  have : StrongEpi p := strongEpi_of_epi p
  let sq : CommSq gi p (colimit.ι F i) (f ≫ e.hom) := ⟨by simpa [α] using hgi⟩
  obtain ⟨l⟩ := (inferInstance : sq.HasLift).exists_lift
  refine ⟨i, l.l, (cancel_mono e.hom).1 ?_⟩
  calc
    (l.l ≫ colimit.ι F i ≫ e.inv) ≫ e.hom = l.l ≫ colimit.ι F i := by simp
    _ = f ≫ e.hom := l.fac_right

/-- A morphism from a quasi-compact algebraic space to a presented affine formal
algebraic space factors through one of its affine thickening stages. -/
theorem exists_factor_through_thickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type (u + 1)) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
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
  exact exists_factor_through_thickening_aux B S hS I D (fun _ _ g => (hD g).1) X e Y hYqc f

/-- A morphism from a quasi-compact algebraic space to a presented affine formal
algebraic space factors through one of its affine stages.

Two of the hypotheses of Stacks 0AIA are not asked for, because the argument does not use them.
Of the target, only the presentation `D`, `hD`, `e` is used, so the set-theoretic condition of
Stacks 0AIS -- the other half of being an affine formal algebraic space, and for a formal
spectrum a condition on the size of the site -- is not assumed. Of the transition morphisms of
the presentation, only that they are closed immersions is used, not that they are thickenings:
surjectivity plays no part. The index of the presentation may lie in any universe, provided it
is `u + 1`-small, the colimit being taken in sheaves of `Type (u + 1)`. Of the source, only the
surjective étale cover by a quasi-compact scheme that quasi-compactness provides is used, so `Y`
is not assumed to be an algebraic space. -/
@[stacks 0AIA]
theorem exists_factor_through_thickening'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (I : Type w₁) [Preorder I] [Small.{u + 1} I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : X ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
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
  exact exists_factor_through_thickening_aux B S hS I D hD X e Y hYqc f

end AlgebraicGeometry
