module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Glueing algebraic spaces along an open covering

An fppf sheaf on the big fppf site of `S` which is covered, locally for the fppf topology, by a
coproduct of algebraic-space subfunctors attached through representable open immersions has a
representable diagonal, and the covering map itself is representable.

## Main results

* `AlgebraicGeometry.Space.sheafify_iSup_range_hom_of_isColimit`: the ranges of the legs of a
  colimit cofan of fppf sheaves have sheafified supremum the whole vertex, so every section of
  the vertex lies locally in one of the summands.
* `AlgebraicGeometry.Space.sieveOfSection_iSup_range_mem`: every section of a presheaf lies, on a
  covering sieve, in the range of one of a family of morphisms whose ranges have sheafified
  supremum the whole presheaf.
* `AlgebraicGeometry.Space.sheafify_iSup_range_comp`: such a covering family may be composed
  with a locally surjective morphism.
* `AlgebraicGeometry.Space.isRepresentable_of_locally_covering`: a sheaf mapping to a presheaf
  `K` is representable as soon as its base changes along a family of representable open
  immersions whose ranges cover `K` are representable.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_openCover`: the covered sheaf has a
  representable diagonal.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_openCover`: the covering map from the
  coproduct of the members to the covered sheaf is relatively representable.

## Implementation notes

The covering condition is carried as the single equation
`(⨆ i, Subfunctor.range (c i)).sheafify J = ⊤` on a family of morphisms `c i : Ci i ⟶ K` of
presheaves, rather than as local surjectivity of a map out of a coproduct, so that it applies
both to the legs of a coproduct cofan and to their composites with the covering map.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0024](https://stacks.math.columbia.edu/tag/0024)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ranges of the legs of a colimit cofan of sheaves have sheafified supremum the whole
sheaf: every section of the vertex lies locally in one of the summands. -/
theorem sheafify_iSup_range_hom_of_isColimit
    {I : Type v} {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (j : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G j)) :
    (⨆ i, Subfunctor.range (j i).hom).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  classical
  have hGsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) G.obj :=
    (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) _).mp G.property
  let K : Subfunctor G.obj := ⨆ i, Subfunctor.range (j i).hom
  let Ksh : Subfunctor G.obj := K.sheafify (BigFppfOver.topology B S hS)
  let Gsh : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨Ksh.toFunctor, (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) _).mpr
      (K.sheafify_isSheaf hGsheaf)⟩
  have hle (i : I) : Subfunctor.range (j i).hom ≤ K :=
    le_iSup (fun k => Subfunctor.range (j k).hom) i
  let m (i : I) : Fi i ⟶ Gsh :=
    ⟨Subfunctor.toRange (j i).hom ≫ Subfunctor.homOfLe (hle i) ≫
      Subfunctor.homOfLe (K.le_sheafify (BigFppfOver.topology B S hS))⟩
  let incl : Gsh ⟶ G := ⟨Ksh.ι⟩
  have hm (i : I) : m i ≫ incl = j i := by
    apply Sheaf.hom_ext
    ext X y
    rfl
  let desc : G ⟶ Gsh := hcoprod.desc (Cofan.mk Gsh m)
  have hsplit : desc ≫ incl = 𝟙 G := by
    apply hcoprod.hom_ext
    rintro ⟨i⟩
    exact (Category.assoc _ _ _).symm.trans <| (hcoprod.fac (Cofan.mk Gsh m) ⟨i⟩ =≫ incl).trans <|
      (hm i).trans (Category.comp_id _).symm
  have hsplit' : desc.hom ≫ Ksh.ι = 𝟙 G.obj := congrArg (fun x : G ⟶ G => x.hom) hsplit
  have hiso : IsIso Ksh.ι := by
    refine ⟨desc.hom, ?_, hsplit'⟩
    apply (cancel_mono Ksh.ι).1
    rw [Category.assoc, hsplit', Category.comp_id, Category.id_comp]
  exact (Subfunctor.eq_top_iff_isIso Ksh).2 hiso


/-- Every section of a presheaf lies, on a covering sieve, in the range of one of a family of
morphisms whose ranges have sheafified supremum the whole presheaf. -/
theorem sieveOfSection_iSup_range_mem
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type*}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    {U : (BigFppfOver B S hS)ᵒᵖ} (t : K.obj U) :
    (⨆ i, Subfunctor.range (c i)).sieveOfSection t ∈
      BigFppfOver.topology B S hS (unop U) := by
  have ht : t ∈ ((⨆ i, Subfunctor.range (c i)).sheafify
      (BigFppfOver.topology B S hS)).obj U := by
    rw [hcov]; trivial
  exact ht

/-- A section on which a morphism in the sieve of a family of morphisms with covering ranges
restricts lies in the range of one of the morphisms. -/
private theorem exists_app_eq_of_mem_sieveOfSection
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type*}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    {U : (BigFppfOver B S hS)ᵒᵖ} {W : BigFppfOver B S hS} (z : K.obj U) {f : W ⟶ unop U}
    (hf : ((⨆ i, Subfunctor.range (c i)).sieveOfSection z).arrows f) :
    ∃ i y, (c i).app (op W) y = K.map f.op z := by
  have hf' : K.map f.op z ∈ (⨆ i, Subfunctor.range (c i)).obj (op W) := hf
  rw [Subfunctor.iSup_obj] at hf'
  simpa using hf'

/-- Composing a family of morphisms whose ranges cover their target with a locally surjective
morphism again gives a family whose ranges cover. -/
theorem sheafify_iSup_range_comp
    {K F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type*}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K) (g : K ⟶ F)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hg : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g) :
    (⨆ i, Subfunctor.range (c i ≫ g)).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  rw [eq_top_iff]
  intro U t _
  show (⨆ i, Subfunctor.range (c i ≫ g)).sieveOfSection t ∈
    BigFppfOver.topology B S hS (unop U)
  refine (BigFppfOver.topology B S hS).transitive (Presheaf.imageSieve_mem _ g t) _ ?_
  rintro V f ⟨z, hz⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieveOfSection_iSup_range_mem B S hS c hcov (U := op V) z)
  rintro W f2 hf2
  obtain ⟨i, y, hy⟩ := exists_app_eq_of_mem_sieveOfSection B S hS c z hf2
  have hmem : F.map (f2 ≫ f).op t ∈ (Subfunctor.range (c i ≫ g)).obj (op W) := by
    refine ⟨y, ?_⟩
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hy, NatTrans.naturality_apply g f2.op z, hz,
      op_comp, F.map_comp, ConcreteCategory.comp_apply]
  show F.map (f2 ≫ f).op t ∈ (⨆ i, Subfunctor.range (c i ≫ g)).obj (op W)
  rw [Subfunctor.iSup_obj]
  exact Set.mem_iUnion.2 ⟨i, hmem⟩

/-- A sheaf with a morphism to a presheaf `K` whose base changes along a family of representable
open immersions covering `K` are representable is itself representable. -/
theorem isRepresentable_of_locally_covering
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {I : Type u} (hI : #I < B.cutoff.ord.cof)
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (h : H.obj ⟶ K)
    {X : I → BigFppfOver B S hS}
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj) (q : ∀ i, yoneda.obj (X i) ⟶ Ci i)
    (hp : ∀ i, IsPullback (p i) (q i) h (c i)) :
    H.obj.IsRepresentable := by
  classical
  have hpopen (i : I) : (openImmersionOver B S hS).presheaf (p i) :=
    (MorphismProperty.relative_isStableUnderBaseChange (openImmersionOver B S hS)).of_isPullback
      (hp i).flip (hopen i)
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc p) := by
    constructor
    intro U s
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (sieveOfSection_iSup_range_mem B S hS c hcov (U := op U) (h.app (op U) s))
    rintro W f2 hf2
    obtain ⟨i, y, hy⟩ := exists_app_eq_of_mem_sieveOfSection B S hS c _ hf2
    let sig : yoneda.obj W ⟶ H.obj := yonedaEquiv.symm (H.obj.map f2.op s)
    let tau : yoneda.obj W ⟶ Ci i := yonedaEquiv.symm y
    have hcomm : sig ≫ h = tau ≫ c i := yonedaEquiv.injective <| by
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hy,
        NatTrans.naturality_apply h f2.op s]
    refine ⟨(Sigma.ι (fun k => yoneda.obj (X k)) i).app (op W)
      (yonedaEquiv ((hp i).lift sig tau hcomm)), ?_⟩
    rw [← FunctorToTypes.comp, Sigma.ι_desc, ← yonedaEquiv_comp, (hp i).lift_fst,
      Equiv.apply_symm_apply]
  exact isRepresentable_of_openCover p hpopen hI hsurj

/-- The pullback in the category of sheaves of two maps into a sheaf is a pullback of presheaves. -/
private theorem exists_isPullback_sheaf
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type u)} (α : X.obj ⟶ F) (β : Y.obj ⟶ F) :
    ∃ (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (f : H.obj ⟶ X.obj) (g : H.obj ⟶ Y.obj),
      IsPullback f g α β := by
  let Fs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  let αs : X ⟶ Fs := ⟨α⟩
  let βs : Y ⟶ Fs := ⟨β⟩
  exact ⟨pullback αs βs, _, _, (IsPullback.of_hasPullback αs βs).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))⟩

/-- An fppf sheaf with a locally surjective coproduct decomposition into algebraic-space
subfunctors by representable open immersions has a representable diagonal. -/
theorem relativelyRepresentable_diag_of_openCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type u} (hI : #I < B.cutoff.ord.cof)
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hFi : ∀ i, IsAlgebraicSpace B S hS (Fi i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf ((jj i).hom ≫ g))
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g) :
    yoneda.relativelyRepresentable (diag F) := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  let _ := B.hasPullbacks_schemes
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hcovF : (⨆ i, Subfunctor.range ((jj i).hom ≫ g)).sheafify
      (BigFppfOver.topology B S hS) = ⊤ :=
    sheafify_iSup_range_comp B S hS (fun i => (jj i).hom) g
      (sheafify_iSup_range_hom_of_isColimit B S hS jj hcoprod) hsurj
  refine ((yoneda_relativelyRepresentable_diag_tfae F).out 3 1).1 ?_
  intro V W ξ ξ'
  set α : yoneda.obj V ⟶ F := yonedaEquiv.symm ξ
  set β : yoneda.obj W ⟶ F := yonedaEquiv.symm ξ'
  obtain ⟨H, fstH, sndH, hH⟩ := exists_isPullback_sheaf B S hS hF
    (X := (BigFppfOver.topology B S hS).yoneda.obj V)
    (Y := (BigFppfOver.topology B S hS).yoneda.obj W) α β
  have hdata : ∀ i, ∃ (Z : BigFppfOver B S hS) (p0 : yoneda.obj Z ⟶ H.obj)
      (q0 : yoneda.obj Z ⟶ (Fi i).obj),
      IsPullback p0 q0 (fstH ≫ α) ((jj i).hom ≫ g) := by
    intro i
    have hA : IsPullback ((hopen i).rep.fst α) (yoneda.map ((hopen i).rep.snd α))
        ((jj i).hom ≫ g) α := (hopen i).rep.isPullback α
    have hB : IsPullback ((hopen i).rep.fst β) (yoneda.map ((hopen i).rep.snd β))
        ((jj i).hom ≫ g) β := (hopen i).rep.isPullback β
    obtain ⟨Z, si, ti, hX⟩ :=
      (Functor.relativelyRepresentable.diag_iff.1 (hFi i).diagonal_representable
        ((hopen i).rep.fst α)) ((hopen i).rep.fst β)
    have T1 := hX.paste_vert hB
    rw [hA.w] at T1
    have hcompat : (ti ≫ yoneda.map ((hopen i).rep.snd α)) ≫ α =
        (yoneda.map si ≫ yoneda.map ((hopen i).rep.snd β)) ≫ β := by
      rw [Category.assoc]; exact T1.w
    let p0 : yoneda.obj Z ⟶ H.obj :=
      hH.lift (ti ≫ yoneda.map ((hopen i).rep.snd α))
        (yoneda.map si ≫ yoneda.map ((hopen i).rep.snd β)) hcompat
    have hpf : p0 ≫ fstH = ti ≫ yoneda.map ((hopen i).rep.snd α) := hH.lift_fst _ _ _
    have hps : p0 ≫ sndH = yoneda.map si ≫ yoneda.map ((hopen i).rep.snd β) :=
      hH.lift_snd _ _ _
    rw [← hps] at T1
    have U1 : IsPullback ti p0 (yoneda.map ((hopen i).rep.snd α)) fstH :=
      IsPullback.of_bot T1 hpf.symm hH
    exact ⟨Z, p0, ti ≫ (hopen i).rep.fst α, U1.flip.paste_vert hA.flip⟩
  choose X p q hp using hdata
  have hrep : H.obj.IsRepresentable :=
    isRepresentable_of_locally_covering B S hS hI (fun i => (jj i).hom ≫ g) hcovF hopen
      H (fstH ≫ α) p q hp
  let _ := hrep
  exact isRepresentable_of_natIso H.obj hH.isoPullback

/-- The map to an fppf sheaf `F` from a coproduct of sheaves whose legs, composed with it, are
representable open immersions is relatively representable. -/
theorem relativelyRepresentable_of_openCover
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {I : Type u} (hI : #I < B.cutoff.ord.cof)
    {Fi : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (jj : ∀ i, Fi i ⟶ G) (hcoprod : IsColimit (Cofan.mk G jj))
    (g : G.obj ⟶ F)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf ((jj i).hom ≫ g)) :
    yoneda.relativelyRepresentable g := by
  classical
  let _ : (BigFppfOver.topology B S hS).Subcanonical := BigFppfOver.subcanonical B S hS
  have hcovG := sheafify_iSup_range_hom_of_isColimit B S hS jj hcoprod
  have hopenj (i : I) : (openImmersionOver B S hS).presheaf (jj i).hom :=
    isOpenImmersion_coproductInj B S hS I Fi G jj hcoprod i
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro V ξ
  set γ : yoneda.obj V ⟶ F := yonedaEquiv.symm ξ
  obtain ⟨H, fstH, sndH, hH⟩ := exists_isPullback_sheaf B S hS hF
    (X := (BigFppfOver.topology B S hS).yoneda.obj V) (Y := G) γ g
  have hdata : ∀ i, ∃ (Z : BigFppfOver B S hS) (p0 : yoneda.obj Z ⟶ H.obj)
      (q0 : yoneda.obj Z ⟶ (Fi i).obj), IsPullback p0 q0 sndH (jj i).hom := by
    intro i
    have hsq : IsPullback ((hopen i).rep.fst γ) (yoneda.map ((hopen i).rep.snd γ))
        ((jj i).hom ≫ g) γ := (hopen i).rep.isPullback γ
    have hc : yoneda.map ((hopen i).rep.snd γ) ≫ γ =
        ((hopen i).rep.fst γ ≫ (jj i).hom) ≫ g := by
      rw [Category.assoc]; exact hsq.w.symm
    let p0 : yoneda.obj ((hopen i).rep.pullback γ) ⟶ H.obj :=
      hH.lift (yoneda.map ((hopen i).rep.snd γ))
        ((hopen i).rep.fst γ ≫ (jj i).hom) hc
    have hps : p0 ≫ sndH = (hopen i).rep.fst γ ≫ (jj i).hom := hH.lift_snd _ _ _
    rw [← hH.lift_fst (yoneda.map ((hopen i).rep.snd γ))
      ((hopen i).rep.fst γ ≫ (jj i).hom) hc] at hsq
    exact ⟨_, p0, (hopen i).rep.fst γ, (IsPullback.of_bot hsq hps.symm hH.flip).flip⟩
  choose X p q hp using hdata
  have hrep : H.obj.IsRepresentable :=
    isRepresentable_of_locally_covering B S hS hI (fun i => (jj i).hom) hcovG hopenj
      H sndH p q hp
  let _ := hrep
  exact isRepresentable_of_natIso H.obj hH.isoPullback

end AlgebraicGeometry.Space

end
