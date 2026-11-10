module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringOfOpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
public import StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections

/-!
# Properness from one covering of the target as in Definition 0AIM

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves over `S`. Condition (5) of **Stacks 0ART** asks for *one* covering `{Y_i ⟶ Y}` of the
target as in Definition 0AIM — by affine formal algebraic spaces, along morphisms representable
by algebraic spaces and étale, jointly surjective as a map of sheaves — whose base changes of
`f` are all proper. This file proves that this one covering already forces `f` to be proper,
which is the implication (5) ⇒ (1) of Stacks 0ART.

## Main results

* `AlgebraicGeometry.FormalSpace.HasProperFormalAtlas.isProper`: **Stacks 0ART, (5) implies
  (1)**.

## Implementation notes

Properness is tested at one scheme-valued point `ξ : U ⟶ Y` at a time, and it descends along a
single surjective étale morphism of the site onto `U`
(`AlgebraicGeometry.FormalSpace.isProper_of_forall_surjective_etale_cover`). So the whole
content is the construction of that morphism out of condition (5), together with the base
change of `f` over it. It is done in three steps.

*One affine étale neighbourhood of each point of `U`.* Joint surjectivity of the covering is
the hypothesis that `⨿ᵢ Y_i ⟶ Y` is locally surjective, equivalently an epimorphism of
sheaves, and a section of the target of an epimorphism out of a coproduct lies, on a covering
sieve, in the image of a *single* summand
(`Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc`). Applied to the section of `Y`
carried by `ξ` this gives a covering sieve of `U` each of whose members factors `ξ` through one
`c i`, and such a sieve contains a jointly surjective family
(`AlgebraicGeometry.exists_family_of_mem_topology`). The members of that family are only flat
and locally of finite presentation, not étale, so they are not themselves usable; instead the
base change `Y_i ×_Y U` is an algebraic space étale over `U` — `c i` being representable by
algebraic spaces and étale — and an atlas `V ⟶ U` of it is a morphism of the site, étale on
underlying schemes, whose image contains the point in question because the flat member of the
family factors through `Y_i ×_Y U` and the atlas is surjective after that base change. An
affine open of `V` around a preimage of the point finishes the step, and the morphism out of it
is étale with affine source, hence of size at most that of `U`.

*A `u`-small family.* The index set of condition (5) lives in `Type (u + 1)`, and a
`Type (u + 1)`-indexed family has no coproduct inside the site: the site's cutoff bounds
cardinals of `Type u`. The family is therefore reindexed by the *affine opens of `U`* — there
are at most `size U` of them — keeping, for each affine open contained in the image of one of
the neighbourhoods above, one such neighbourhood. The images are open because an étale morphism
is open, so the retained neighbourhoods still cover `U`.

*The coproduct.* The coproduct `U'` of that family lies in the site under the uniform bound
`size U`, and the induced `q : U' ⟶ U` is surjective and étale
(`AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_etaleCover`). The base change
of `f` over `U'` is the coproduct of its base changes over the members, coproducts of sheaves of
sets being van Kampen (`CategoryTheory.Sheaf.isColimitCofanMkPullback`), and each of those is
the base change of a proper `X ×_Y Y_i ⟶ Y_i` along the factorisation, hence — reading
Stacks 0ART (3) ⇒ (4) at an affine — an algebraic space proper over an affine member. The
coproduct is then an algebraic space by **Stacks 02WQ** in the value universe `Type (u + 1)`,
the uniform bound on the atlases needed for that being supplied by properness
(`AlgebraicGeometry.Space.exists_affine_atlas_size_le_of_isProperULift`), and it is proper over
`U'` by **Stacks 0422** along the open-immersion family of the members of the coproduct.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0ART](https://stacks.math.columbia.edu/tag/0ART)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale neighbourhood of a point of a scheme-valued point of the target, over
which the point factors through one member of the covering.** For a covering `{c i : Y_i ⟶ Y}`
as in Definition 0AIM, a scheme-valued point `ξ : U ⟶ Y` and a point `x` of `U`, there is an
affine object `A` of the site and a morphism `a : A ⟶ U` of the site, étale on underlying
schemes and with `x` in its image, such that `ξ` restricted along `a` factors through one
`c i`.

A section of `Y` lies locally in the image of one summand of `⨿ᵢ Y_i`, so a covering sieve of
`U` has all its members factoring through some `c i`; such a sieve is jointly surjective on
points, but by flat morphisms, so the étale neighbourhood is taken instead inside an atlas of
the algebraic space `Y_i ×_Y U`, which is étale over `U`. -/
private theorem exists_affine_etale_factorization
    {Y : FppfSheaf B S hS} {I : Type (u + 1)} {Yi : I → FppfSheaf B S hS}
    (c : ∀ i, Yi i ⟶ Y)
    (hce : ∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci)
    (hls : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (A : BigFppfOver B S hS) (a : A ⟶ U) (i : I)
      (r : (uliftYoneda.{u + 1}).obj A ⟶ (Yi i).obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Etale ((BigFppfOver.toScheme B S hS).map a) ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map a) ∧
      r ≫ (c i).hom = (uliftYoneda.{u + 1}).map a ≫ ξ := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Epi (Sigma.desc c) := (Sheaf.isLocallySurjective_iff_epi _).1 hls
  -- the section of `Y` over `U` carried by `ξ`
  obtain ⟨R, hR, hRfac⟩ := Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc Yi c U
    (uliftYonedaEquiv.{u + 1} ξ)
  -- a jointly surjective family inside the covering sieve
  obtain ⟨J, W, m, hmR, -, -, hmcov⟩ :=
    AlgebraicGeometry.exists_family_of_mem_topology B S hS hR
  obtain ⟨k, hk⟩ := hmcov x
  set g : (Over.mk (m k ≫ U.hom) : BigFppfOver B S hS) ⟶ U := Over.homMk (m k)
  obtain ⟨i, a₀, ha₀⟩ := hRfac g (hmR k)
  -- the factorisation of `ξ` restricted along `g` through `c i`
  have hρ : uliftYonedaEquiv.{u + 1}.symm a₀ ≫ (c i).hom
      = (uliftYoneda.{u + 1}).map g ≫ ξ := by
    apply uliftYonedaEquiv.{u + 1}.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, ha₀]
    exact uliftYonedaEquiv_naturality.{u + 1} ξ g.op
  -- the base change of `c i` along `ξ`, an algebraic space étale over `U`
  obtain ⟨hci, hcie⟩ := hce i
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ (c i).hom) := hci U ξ
  obtain ⟨V, α, hαsurj, hαet⟩ := hPalg.exists_atlas
  -- the atlas of that base change, as a morphism of the site étale over `U`
  set v : V ⟶ U := (uliftYoneda.{u + 1}).preimage (α ≫ pullback.fst ξ (c i).hom)
  have hvmap : (uliftYoneda.{u + 1}).map v = α ≫ pullback.fst ξ (c i).hom :=
    (uliftYoneda.{u + 1}).map_preimage _
  have hvet : Etale ((BigFppfOver.toScheme B S hS).map v) :=
    (Space.relative_etale_uliftYoneda_map_iff.{u + 1} B S hS v).1
      (by rw [hvmap]; exact hcie U ξ V α hαet)
  -- the point `x` is in the image of the atlas, read through the sieve member `g`
  set γ : (uliftYoneda.{u + 1}).obj (Over.mk (m k ≫ U.hom)) ⟶ pullback ξ (c i).hom :=
    pullback.lift ((uliftYoneda.{u + 1}).map g) (uliftYonedaEquiv.{u + 1}.symm a₀) hρ.symm
    with hγ
  have hαrep : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable α :=
    hαsurj.1
  have hssurj : Surjective ((BigFppfOver.toScheme B S hS).map (hαrep.snd γ)) :=
    hαsurj.2 γ (hαrep.fst γ) (hαrep.snd γ) (hαrep.isPullback γ)
  have htv : hαrep.fst' γ ≫ v = hαrep.snd γ ≫ g := by
    apply (uliftYoneda.{u + 1}).map_injective
    rw [Functor.map_comp, Functor.map_comp, hvmap, hαrep.map_fst', ← Category.assoc,
      hαrep.w γ, Category.assoc]
    congr 1
    rw [hγ, pullback.lift_fst]
  obtain ⟨w, hw⟩ := hk
  obtain ⟨z, hz⟩ := hssurj.1 w
  have hxv : x ∈ Set.range ((BigFppfOver.toScheme B S hS).map v) := by
    refine ⟨((BigFppfOver.toScheme B S hS).map (hαrep.fst' γ)) z, ?_⟩
    have h1 : ((BigFppfOver.toScheme B S hS).map (hαrep.fst' γ ≫ v)) z = x := by
      rw [htv]
      change ((BigFppfOver.toScheme B S hS).map g)
        (((BigFppfOver.toScheme B S hS).map (hαrep.snd γ)) z) = x
      rw [hz]
      exact hw
    simpa using h1
  obtain ⟨y, hy⟩ := hxv
  -- an affine open of the atlas around a preimage of `x`, as an object of the site
  obtain ⟨O, hyO⟩ : ∃ O : ((BigFppfOver.toScheme B S hS).obj V).affineOpens, y ∈ O.1 :=
    TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top ((BigFppfOver.toScheme B S hS).obj V)).ge (Set.mem_univ y))
  have hcon : B.Contains (O.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion O.1.ι V.left.property
  set fO : B.obj hcon ⟶ V.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj hcon) ⟶ B.inclusion.obj V.left from O.1.ι)
  set A : BigFppfOver B S hS := Over.mk (fO ≫ V.hom)
  set gA : A ⟶ V := Over.homMk fO rfl
  have hgAmap : (BigFppfOver.toScheme B S hS).map gA = O.1.ι := B.inclusion.map_preimage _
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := O.2
  refine ⟨A, gA ≫ v, i,
    (uliftYoneda.{u + 1}).map gA ≫ α ≫ pullback.snd ξ (c i).hom, hAaff, ?_, ?_, ?_⟩
  · rw [Functor.map_comp, hgAmap]
    have _ := hvet
    infer_instance
  · refine ⟨⟨y, hyO⟩, ?_⟩
    rw [Functor.map_comp, hgAmap]
    exact hy
  · rw [Functor.map_comp, Category.assoc, Category.assoc, Category.assoc,
      ← pullback.condition, hvmap, Category.assoc]

/-- **A `u`-small affine étale covering of a scheme-valued point of the target, each member
factoring through one member of the covering of Definition 0AIM.** The neighbourhoods of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_factorization` are reindexed by the affine
opens of `U`, of which there are at most `size U`: an étale morphism is open, so each point of
`U` has an affine open neighbourhood inside the image of one of them, and keeping one
neighbourhood per affine open of `U` that admits one leaves a covering family. -/
private theorem exists_affine_etale_family
    {Y : FppfSheaf B S hS} {I : Type (u + 1)} {Yi : I → FppfSheaf B S hS}
    (c : ∀ i, Yi i ⟶ Y)
    (hce : ∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci)
    (hls : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj) :
    ∃ (K : Type u) (A : K → BigFppfOver B S hS) (a : ∀ j, A j ⟶ U) (idx : K → I)
      (r : ∀ j, (uliftYoneda.{u + 1}).obj (A j) ⟶ (Yi (idx j)).obj),
      #K ≤ ((BigFppfOver.toScheme B S hS).obj U).size ∧
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (A j))) ∧
      (∀ j, Etale ((BigFppfOver.toScheme B S hS).map (a j))) ∧
      (∀ x : (BigFppfOver.toScheme B S hS).obj U,
        ∃ j, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (a j))) ∧
      ∀ j, r j ≫ (c (idx j)).hom = (uliftYoneda.{u + 1}).map (a j) ≫ ξ := by
  classical
  set Q : ((BigFppfOver.toScheme B S hS).obj U).affineOpens → Prop := fun O =>
    ∃ (A : BigFppfOver B S hS) (a : A ⟶ U) (i : I)
      (r : (uliftYoneda.{u + 1}).obj A ⟶ (Yi i).obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Etale ((BigFppfOver.toScheme B S hS).map a) ∧
      (O.1 : Set ((BigFppfOver.toScheme B S hS).obj U)) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map a) ∧
      r ≫ (c i).hom = (uliftYoneda.{u + 1}).map a ≫ ξ
  choose A a idx r hAaff hAet hAsub hAfac using fun j : {O // Q O} => j.2
  refine ⟨{O // Q O}, A, a, idx, r, ?_, hAaff, hAet, ?_, hAfac⟩
  · exact (Cardinal.mk_subtype_le _).trans
      (Scheme.mk_affineOpens_le_size ((BigFppfOver.toScheme B S hS).obj U))
  · intro x
    obtain ⟨A₀, a₀, i₀, r₀, hA₀aff, hA₀et, hx₀, hfac₀⟩ :=
      exists_affine_etale_factorization B S hS c hce hls U ξ x
    have hopen : IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map a₀)) :=
      ((BigFppfOver.toScheme B S hS).map a₀).isOpenMap.isOpen_range
    obtain ⟨-, ⟨O, hO, rfl⟩, hxO, hOsub⟩ :=
      ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
        hx₀ hopen
    exact ⟨⟨⟨O, hO⟩, A₀, a₀, i₀, r₀, hA₀aff, hA₀et, hOsub, hfac₀⟩,
      hAsub _ hxO⟩

/-- **One surjective étale morphism of the site onto a scheme-valued point of the target, over
which the base change of `f` is an algebraic space proper over the source.** This is the input
that `AlgebraicGeometry.FormalSpace.isProper_of_forall_surjective_etale_cover` asks for, built
from condition (5) of Stacks 0ART at one scheme-valued point of `Y`.

The morphism is the coproduct of the affine étale neighbourhoods of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_family`, which lies in the site under the
uniform bound `size U`. Over it the base change of `f` is the coproduct of the base changes over
the members, each of which is an algebraic space proper over an affine object of the site
because it is a base change of one of the proper morphisms of condition (5). -/
private theorem exists_etale_cover_of_hasProperFormalAtlas
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y} {I : Type (u + 1)} {Yi : I → FppfSheaf B S hS}
    (c : ∀ i, Yi i ⟶ Y)
    (hce : ∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci)
    (hls : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc c))
    (hprop : ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → IsProper B S hS p)
    (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj) :
    ∃ (U' : BigFppfOver B S hS) (q : U' ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) ∧
      Space.IsProperULift.{u + 1} B S hS
        (pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) := by
  classical
  obtain ⟨K, A, a, idx, r, hK, hAaff, hAet, hAcov, hAfac⟩ :=
    exists_affine_etale_family B S hS c hce hls U ξ
  have hAsize : ∀ j, ((BigFppfOver.toScheme B S hS).obj (A j)).size ≤
      ((BigFppfOver.toScheme B S hS).obj U).size := by
    intro j
    have _ := hAaff j
    have _ := hAet j
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (a j))
  obtain ⟨V, jj, q, hjq, hjopen, hjcov, hqsurj, hqet, -, ⟨hjsheaf⟩⟩ :=
    BigFppfOver.exists_surjective_etale_sigma_of_etaleCover B S hS A U a hAet hAcov
      U.left.property hK hAsize
  -- the base change of `f` over the coproduct, at the level of sheaves
  have : Small.{u + 1} K := ⟨⟨ULift.{u + 1} K, ⟨Equiv.ulift.symm⟩⟩⟩
  set ζ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ Y :=
    ObjectProperty.homMk ((uliftYoneda.{u + 1}).map q ≫ ξ)
  set π : pullback ζ f ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V :=
    pullback.fst ζ f
  have hApb : IsPullback π (pullback.snd ζ f) ζ f := IsPullback.of_hasPullback ζ f
  set ιj : ∀ j, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (A j) ⟶
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V :=
    fun j => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (jj j)
  -- the factorisation of each summand through one member of the covering
  set ρ : ∀ j, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (A j) ⟶ Yi (idx j) :=
    fun j => ObjectProperty.homMk (r j)
  have hσ : ∀ j, ρ j ≫ c (idx j) = ιj j ≫ ζ := by
    intro j
    refine Sheaf.hom_ext ?_
    change r j ≫ (c (idx j)).hom =
      (uliftYoneda.{u + 1}).map (jj j) ≫ (uliftYoneda.{u + 1}).map q ≫ ξ
    rw [hAfac j, ← Category.assoc, ← Functor.map_comp, hjq j]
  -- each summand of that base change is an algebraic space proper over an affine
  have hsummand : ∀ j, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback (ιj j) π).obj ∧
      Space.IsProperULift.{u + 1} B S hS (pullback.fst (ιj j) π).hom := by
    intro j
    have houter : IsPullback (pullback.snd (ιj j) π ≫ pullback.snd ζ f)
        (pullback.fst (ιj j) π) f (ρ j ≫ c (idx j)) := by
      rw [hσ j]
      exact (IsPullback.of_hasPullback (ιj j) π).flip.paste_horiz hApb.flip
    have hleft := (IsPullback.of_right' houter
      (IsPullback.of_hasPullback (c (idx j)) f).flip).flip
    have hpi : IsProper B S hS (pullback.fst (c (idx j)) f) :=
      hprop (idx j) _ (pullback.fst (c (idx j)) f) (pullback.snd (c (idx j)) f)
        (IsPullback.of_hasPullback _ _)
    have hpj : IsProper B S hS (pullback.fst (ιj j) π) :=
      IsProper.of_isPullback B S hS hleft hpi
    exact ((hpj.isProperOnSchemeBaseChanges B S hS).isProperOnAffineBaseChanges B
      S hS).isAlgebraicAndProper B S hS (A j) (hAaff j) (𝟙 _) (pullback (ιj j) π)
      (pullback.fst (ιj j) π) (𝟙 _) IsPullback.of_id_snd
  -- the base change over the coproduct is the coproduct of those summands
  have hZcofan : IsColimit (Cofan.mk (pullback ζ f) fun j => pullback.snd (ιj j) π) :=
    Sheaf.isColimitCofanMkPullback (BigFppfOver.topology B S hS) ιj hjsheaf π
  have halgZ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ζ f).obj := by
    choose T atl hTaff hTsurj hTet hTsize using fun j =>
      Space.exists_affine_atlas_size_le_of_isProperULift.{u + 1} B S hS (hAaff j)
        (hsummand j).1 (pullback.fst (ιj j) π).hom (hsummand j).2
    exact Space.isAlgebraicSpaceULift_coproduct_of_size_le.{u + 1} B S hS
      (fun j => (hsummand j).1) (fun j => pullback.snd (ιj j) π) hZcofan T atl hTsurj hTet
      (Scheme.aleph0_le_size _) U.left.property hK
      (fun j => (hTsize j).trans (hAsize j))
  have hproperZ : Space.IsProperULift.{u + 1} B S hS π.hom := by
    refine Space.isProperULift_of_isPullback_uliftYoneda_family.{u} B S hS
      (V := fun i : ULift.{u + 1} K => A i.down) (q := fun i => jj i.down)
      (p' := fun i => (pullback.fst (ιj i.down) π).hom)
      (k := fun i => (pullback.snd (ιj i.down) π).hom) (fun i => ?_) halgZ ?_
      (fun i => (hsummand i.down).2)
    · exact ((IsPullback.of_hasPullback (ιj i.down) π).map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).flip
    · exact Space.isFppfCovering_yoneda_of_openCover B S hS
        (fun i : ULift.{u + 1} K => A i.down) (fun i => jj i.down)
        (fun i => hjopen i.down) (fun x => (hjcov x).elim fun j hj => ⟨⟨j⟩, hj⟩)
  -- transport to the chosen fibre product of presheaves
  have hpre : IsPullback π.hom (pullback.snd ζ f).hom
      ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom :=
    hApb.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (pullback ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hpre.isoPullback halgZ
  refine ⟨V, q, hqsurj, hqet, halg, ?_⟩
  have h1 := Space.isProperULift_precomp.{u + 1} B S hS hpre.isoPullback.symm π.hom halg halgZ
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V) hproperZ
  have h2 : hpre.isoPullback.symm.hom ≫ π.hom =
      pullback.fst ((uliftYoneda.{u + 1}).map q ≫ ξ) f.hom :=
    (Iso.inv_comp_eq _).2 hpre.isoPullback_hom_fst.symm
  rwa [h2] at h1

/-- **Stacks 0ART, (5) implies (1).** A morphism of formal algebraic spaces over `S` admitting
*one* covering of its target as in Definition 0AIM all of whose base changes of the morphism are
proper is itself proper.

Properness is local on the target for a surjective étale covering by one object of the site, and
such a covering of each scheme-valued point of `Y` is assembled from the given covering: its
joint surjectivity puts every point of the scheme-valued point inside an affine étale
neighbourhood over which the point factors through one member of the covering, and the
coproduct of a `u`-small refinement of those neighbourhoods is the covering object. -/
@[stacks 0ART "(5) implies (1)"]
theorem HasProperFormalAtlas.isProper {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasProperFormalAtlas B S hS f) : IsProper B S hS f := by
  obtain ⟨I, Yi, c, -, hce, hls, hprop⟩ := h
  exact isProper_of_forall_surjective_etale_cover B S hS f
    (exists_etale_cover_of_hasProperFormalAtlas B S hS c hce hls hprop)

end AlgebraicGeometry.FormalSpace

end
