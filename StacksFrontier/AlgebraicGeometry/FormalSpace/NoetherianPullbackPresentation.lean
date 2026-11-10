module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Noetherian stages of a pulled-back affine presentation

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves over `S` which is representable by schemes with affine represented base changes. If `Y`
has a presentation by affine thickenings whose stages are Noetherian schemes and `f` is locally
of finite type, then so does `X`: the stages of the presentation of `X` obtained by pulling the
one of `Y` back along `f` are of finite type over the stages of `Y`, hence Noetherian.

This is the half of part (6) of **Stacks 0AKP** which does not pass through a presenting ring.
Part (6) itself says that a Noetherian `Y` and a locally-of-finite-type `f` give a Noetherian
`X`; through the equivalence of conditions (1) and (3) of Stacks 0AKM
(`AlgebraicGeometry.FormalSpace.isNoetherian_tfae`) it is exactly this statement together with
part (5) of Stacks 0AKP, that `X` is adic\* when `Y` is. Both halves are assembled, and the
tag `0AKP` placed, in
`AlgebraicGeometry.FormalSpace.isNoetherian_of_relative_isAffineHom'` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/TypeDescentAlongAffine.lean`; nothing here carries
a `@[stacks 0AKP]` attribute, since on its own it is not a part of the source.

## Main results

* `AlgebraicGeometry.FormalSpace.hasNoetherianAffinePresentation_of_relative_isAffineHom`:
  a Noetherian affine presentation of the target pulls back to one of the source along a
  representable affine morphism which is locally of finite type.

## Implementation notes

The presentation of the source and the cartesian squares identifying its stages are
`AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation`, and its transition
morphisms are thickenings by
`AlgebraicGeometry.FormalSpace.isThickening_of_cartesian_presentation`; only the Noetherian
condition on the stages has to be proved.

A stage of the pulled-back presentation is cartesian over the corresponding stage of `Y`, and
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType` is tested on commuting squares of étale
charts of a represented base change of `f`. The stage square is such a base change: the two
colimit injections are morphisms out of sheafified representables, and the comparison
isomorphism of the cartesian square with the chosen fibre product is an étale chart because an
isomorphism is. Reading the condition off the square needs the underlying presheaf of a
sheafified representable to be the universe-lifted Yoneda presheaf, which is
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'` for the subcanonical big fppf site.

Noetherianness of the stage of the source then follows from Noetherianness of the stage of `Y`,
the morphism between them being locally of finite type; the stage is affine, so quasi-compact,
and only local Noetherianness has to be transported.

## References

* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves on the big fppf site of `S` is an étale chart in the sense of
the universe-lifted relative morphism property: its represented base changes are isomorphisms
of objects of the site, and an isomorphism of schemes is étale. -/
private theorem relative_etale_uliftYoneda_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G) [IsIso a] :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  change Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- A Noetherian affine presentation of the target of a representable affine morphism which is
locally of finite type pulls back to a Noetherian affine presentation of the source. -/
theorem hasNoetherianAffinePresentation_of_relative_isAffineHom
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hY : HasNoetherianAffinePresentation B S hS Y) :
    HasNoetherianAffinePresentation B S hS X := by
  classical
  obtain ⟨I, pre, hI, hdir, D, hD, ⟨eY⟩, hDnoeth⟩ := hY
  let : Preorder I := pre
  let : Nonempty I := hI
  let : IsDirected I (· ≤ ·) := hdir
  obtain ⟨E, p, eX, hcart⟩ := exists_affine_pullback_presentation B S hS f hf D eY
  refine ⟨I, pre, hI, hdir, E,
    isThickening_of_cartesian_presentation B S hS f D E p eY eX hcart hD, ⟨eX⟩, ?_⟩
  intro i
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let Fp := sheafToPresheaf J (Type (u + 1))
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let : J.Subcanonical := inferInstance
  let e : G ⋙ Fp ≅ uliftYoneda.{u + 1} :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' J) Fp ≪≫
      GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1} J
  let U := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let V := (BigAffineFppf.inclusion B S hS).obj (E.obj i)
  let d : G.obj U ⟶ Y :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ eY.inv
  let a : G.obj V ⟶ X :=
    colimit.ι (E ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ eX.inv
  let q : V ⟶ U := (BigAffineFppf.inclusion B S hS).map (p.app i)
  let eU := e.app U
  let eV := e.app V
  let ξ : (uliftYoneda.{u + 1}).obj U ⟶ Fp.obj Y := eU.inv ≫ Fp.map d
  obtain ⟨_, hprop⟩ := hft
  have hs : IsPullback (eV.inv ≫ Fp.map a) ((uliftYoneda.{u + 1}).map q)
      (Fp.map f) ξ := by
    apply IsPullback.of_iso ((hcart i).map Fp) eV (Iso.refl _) eU (Iso.refl _)
    · simp only [Functor.map_comp]
      rw [eV.hom_inv_id_assoc]
      rfl
    · exact e.hom.naturality q
    · simp
    · simp only [Functor.map_comp]
      rw [eU.hom_inv_id_assoc]
      rfl
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) :=
    hprop U ξ V U hs.flip.isoPullback.hom (𝟙 ((uliftYoneda.{u + 1}).obj U)) q
      (relative_etale_uliftYoneda_of_isIso B S hS _)
      (relative_etale_uliftYoneda_of_isIso B S hS _) hs.flip.isoPullback_hom_fst.symm
  have : AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hDnoeth i
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map q) }

end AlgebraicGeometry.FormalSpace

end
