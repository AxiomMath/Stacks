module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# The scheme atlas of a sheaf glued along an open covering

`StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace` proves of an fppf sheaf `F` covered by
algebraic-space subfunctors through representable open immersions that its diagonal is
representable and that the covering map out of the coproduct `G` of the members is relatively
representable. The remaining clause of `AlgebraicGeometry.IsAlgebraicSpace` is the surjective
étale scheme atlas, and that is what this file supplies.

The atlas is not assembled out of the atlases of the members. The coproduct `G` is assumed to be
an algebraic space — this is hypothesis (2)(e) of the source — so it already has an atlas
`a : yoneda.obj V ⟶ G`, and the atlas of `F` is the single composite `a ≫ g`. Its two properties
are then read off `a` and the cover:

* étaleness is locality at the source along the open cover of `V` by the parts `V ×_G Fᵢ` lying
  in the members, since on such a part the atlas factors as an étale morphism to `Fᵢ` followed by
  the open immersion `Fᵢ ⟶ F`;
* surjectivity is local surjectivity of `a ≫ g`, which is local surjectivity of `a` — Stacks 05VM
  applied to the atlas of `G`, étale being flat and locally of finite presentation — composed
  with the assumed local surjectivity of `g`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_mem_range_snd_of_sheafify_iSup` and
  `AlgebraicGeometry.Space.exists_mem_range_snd_of_isColimit`: the parts of a chart of a
  coproduct of fppf sheaves lying in the summands cover the chart. This is the open cover along
  which étaleness of the atlas is checked.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_openCover`: an fppf sheaf with a jointly locally
  surjective family of algebraic-space subfunctors attached through representable open immersions
  is an algebraic space, when the coproduct of the family is one.

## Implementation notes

The index type carries `#I < B.cutoff.ord.cof` and lives in `Type u`. This is inherited, through
`AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover` and
`AlgebraicGeometry.Space.relativelyRepresentable_of_openCover`, from
`AlgebraicGeometry.Space.isRepresentable_of_openCover`, and it is *not* needed for the atlas
clause proved here: the atlas clause uses only that the coproduct is an algebraic space. The
hypothesis is therefore stronger than the mathematics requires, since the object glued inside
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering` is a subobject of a product of two
objects of the site and so has size bounded independently of `#I`. Weakening it is a change to
the gluing theorem, not to this file.

The open cover of the chart `V` of `G` along which étaleness is tested is the family of
represented pullbacks `V ×_G Fᵢ`, which exist because the coproduct inclusions are relatively
representable open immersions by
`AlgebraicGeometry.Space.isOpenImmersion_coproductInj`. That the family covers `V` is the only
point at which the covering hypothesis enters the atlas clause, and it enters through the ranges
of the inclusions into `G`, not of their composites with the covering map: the section of `G`
corresponding to the chart lies, on a covering sieve, in one of the summands, and
`AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology` converts that sieve into an
arrow through a prescribed point, which the universal property of the represented pullback then
factors. No sheafification and no local surjectivity of a map out of a coproduct of the charts is
used.

Local surjectivity of the atlas of `G` is Stacks 05VM, whose hypothesis is a single morphism
property asserting flatness, local finite presentation and surjectivity together. It is built
from the two separate properties carried by
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` by applying both to the *same* base-change
square, so that no two choices of represented pullback have to be compared.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The traces of a covering family on a chart cover the chart.** If the ranges of a family of
relatively representable open immersions `c i` have sheafified supremum the whole of `G`, then
the represented pullbacks `V ×_G Ci i` along a chart `a : yoneda.obj V ⟶ G` of `G` are jointly
surjective on the points of the scheme underlying `V`.

The section of `G` corresponding to `a` lies, on a covering sieve of `V`, in the range of one of
the members; `AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology` picks an arrow of
that sieve through the prescribed point, and the universal property of the represented pullback
factors it. The covering hypothesis is stated as the sheafified supremum rather than through a
colimit cofan, because that is all the argument uses and it makes the lemma reusable for a
family which is not a coproduct decomposition. -/
theorem exists_mem_range_snd_of_sheafify_iSup
    {I : Type v} {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : ∀ i, Ci i ⟶ G}
    (hc : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ G)
    (y : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hc i).rep.snd a)).base := by
  classical
  obtain ⟨W, h, hh, z, hz⟩ := BigFppfOver.exists_mem_range_of_mem_topology B S hS
    (sieveOfSection_iSup_range_mem B S hS c hcov (U := op V) (yonedaEquiv a)) y
  have hh' : G.map h.op (yonedaEquiv a) ∈
      (⨆ i, Subfunctor.range (c i)).obj (op W) := hh
  rw [Subfunctor.iSup_obj] at hh'
  obtain ⟨i, w, hw⟩ : ∃ i, ∃ w,
      (c i).app (op W) w = G.map h.op (yonedaEquiv a) := by simpa using hh'
  have hcomm : yonedaEquiv.symm w ≫ c i = yoneda.map h ≫ a := by
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, ← yonedaEquiv_naturality]
  refine ⟨i, ((BigFppfOver.toScheme B S hS).map
    ((hc i).rep.lift (yonedaEquiv.symm w) h hcomm)).base z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp,
    Functor.relativelyRepresentable.lift_snd]

/-- **The parts of a chart of a coproduct lying in the summands cover the chart.** The colimit
form of `AlgebraicGeometry.Space.exists_mem_range_snd_of_sheafify_iSup`: a colimit cofan is a
covering family by `AlgebraicGeometry.Space.sheafify_iSup_range_hom_of_isColimit`, and that is
the only way the colimit enters. -/
theorem exists_mem_range_snd_of_isColimit
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (hoj : ∀ i, (openImmersionOver B S hS).presheaf (jj i).hom)
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ G.obj)
    (y : (BigFppfOver.toScheme B S hS).obj V) :
    ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((hoj i).rep.snd a)).base :=
  exists_mem_range_snd_of_sheafify_iSup B S hS hoj
    (sheafify_iSup_range_hom_of_isColimit B S hS jj hcoprod) a y

/-- **Stacks 02WR.** An fppf sheaf `F` with a family `Fi` of algebraic-space subfunctors attached
through relatively representable open immersions `(jj i).hom ≫ g`, whose coproduct `G` is an
algebraic space and maps locally surjectively to `F`, is an algebraic space.

The diagonal is `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover`. The atlas is
the composite of an atlas of `G` with the covering map: it is étale by locality at the source
along the open cover of the chart by the parts lying in the members, and surjective because it is
locally surjective. -/
theorem isAlgebraicSpace_of_openCover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (I : Type u) (hI : #I < B.cutoff.ord.cof)
    (Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hFi : ∀ i, IsAlgebraicSpace B S hS (Fi i).obj)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (jj : ∀ i, Fi i ⟶ G)
    (hcoprod : IsColimit (Cofan.mk G jj))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ((jj i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g)
    (hG : IsAlgebraicSpace B S hS G.obj) :
    IsAlgebraicSpace B S hS F := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  let _ := B.hasPullbacks_schemes
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  obtain ⟨V, a, hsurjA, hetA⟩ := hG.exists_atlas
  have hrep : yoneda.relativelyRepresentable (a ≫ g) := MorphismProperty.comp_mem _ _ _ hetA.rep
    (relativelyRepresentable_of_openCover B S hS hF hI jj hcoprod g hopen)
  refine ⟨hF, relativelyRepresentable_diag_of_openCover B S hS hF hI hFi jj hcoprod g hopen hsurj,
    V, a ≫ g, ?_, ?_⟩
  · -- the atlas is surjective, because it is locally surjective
    have hprop : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        ((fun _ _ f => _root_.AlgebraicGeometry.Flat f ∧
            _root_.AlgebraicGeometry.LocallyOfFinitePresentation f ∧
            _root_.AlgebraicGeometry.Surjective f) : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a := by
      refine ⟨hetA.rep, fun A A' ξ fst snd sq => ?_⟩
      have h1 : _root_.AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map snd) := hetA.property ξ fst snd sq
      obtain ⟨hflat, -, hlfp⟩ :=
        _root_.AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.1 h1
      exact ⟨hflat, hlfp, hsurjA.property ξ fst snd sq⟩
    have hlsA : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a :=
      isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
        B S hS (⟨a⟩ : (BigFppfOver.topology B S hS).yoneda.obj V ⟶ G) hprop
    have _ := hlsA
    have _ := hsurj
    have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (a ≫ g) :=
      inferInstance
    exact presheaf_surjective_of_isLocallySurjective B S hS hrep hls
  · -- the atlas is étale, by locality at the source on the parts lying in the members
    have _ : IsZariskiLocalAtSource (@_root_.AlgebraicGeometry.Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @_root_.AlgebraicGeometry.Etale.{u}) (Q := RingHom.Etale)
    have _ := isStableUnderComposition_presheaf_inverseImage B S hS
      (@_root_.AlgebraicGeometry.Etale.{u})
    have hoj : ∀ i, (openImmersionOver B S hS).presheaf (jj i).hom := fun i =>
      isOpenImmersion_coproductInj B S hS I Fi G jj hcoprod i
    have hle : openImmersionOver B S hS ≤ MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u}) (BigFppfOver.toScheme B S hS) := by
      intro X Y f hf
      have _ : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map f) := hf
      change _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map f)
      infer_instance
    refine presheaf_inverseImage_of_isZariskiLocalAtSource B S hS
      (@_root_.AlgebraicGeometry.Etale.{u}) hrep (fun i => (hoj i).rep.snd a)
      (fun i => (hoj i).property_snd a)
      (exists_mem_range_snd_of_isColimit B S hS jj hcoprod hoj a) fun i => ?_
    have hsq : IsPullback ((hoj i).rep.fst a) (yoneda.map ((hoj i).rep.snd a))
      (jj i).hom a := (hoj i).rep.isPullback a
    have hcomp : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf
        ((hoj i).rep.fst a ≫ (jj i).hom ≫ g) :=
      MorphismProperty.comp_mem _ _ _
        ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hetA)
        (MorphismProperty.relative_monotone hle _ (hopen i))
    have heq : (hoj i).rep.fst a ≫ (jj i).hom ≫ g =
        yoneda.map ((hoj i).rep.snd a) ≫ a ≫ g := by
      rw [← Category.assoc, hsq.w, Category.assoc]
    rwa [heq] at hcomp

end AlgebraicGeometry.Space

end
