module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria

/-!
# Algebraicity of the sheaf glued in the excision equivalence

Let `f : V ⟶ W` be an étale morphism of algebraic spaces over a scheme `S` and let `T ⊆ W` be a
closed subspace whose preimage `f⁻¹T` is carried isomorphically onto `T` by `f`. An fppf sheaf `N`
over `W` such that the projection `N ×_W W⁰ ⟶ W⁰` is an isomorphism, where `W⁰ = W ∖ T`, and such
that `N ×_W V` is isomorphic to an algebraic space, is an algebraic space. This is the last step of
the proof of Stacks 0BGY.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isZariskiCover_pullback`: an fppf sheaf over an
  algebraic space `W` whose base change along every member of a finite Zariski covering of `W` is
  an algebraic space is an algebraic space.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isIso_pullback_snd_of_isAlgebraicSpace_pullback`:
  the last step of the proof of Stacks 0BGY.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 040T](https://stacks.math.columbia.edu/tag/040T)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Algebraicity of a sheaf over an algebraic space is detected on a finite Zariski covering
of that space.** Let `W` be an algebraic space over `S`, let `g : N ⟶ W` be a morphism from an
fppf sheaf, and let `{Uᵢ}` be a finite Zariski covering of `W`. If every base change `N ×_W Uᵢ`
is an algebraic space over `S`, then so is `N`. -/
theorem isAlgebraicSpace_of_isZariskiCover_pullback
    {W N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : N ⟶ W)
    (hN : Presheaf.IsSheaf (BigFppfOver.topology B S hS) N)
    {ι : Type u} [Finite ι] (Ufam : ι → Subfunctor W)
    (hcov : IsZariskiCover B S hS ι Ufam)
    (halg : ∀ i, IsAlgebraicSpace B S hS (pullback g (Ufam i).ι)) :
    IsAlgebraicSpace B S hS N := by
  classical
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B S hS) (Type u)
  have _ : HasFiniteCoproducts (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance
  have _ : HasColimitsOfShape (Discrete ι) (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ ι
  set Fs : ι → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun i ↦ ⟨pullback g (Ufam i).ι, (halg i).isSheaf⟩
  set gsh : (∐ Fs) ⟶ (⟨N, hN⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    Sigma.desc fun i ↦ ObjectProperty.homMk (pullback.fst g (Ufam i).ι)
  have hιdesc : ∀ i, (Sigma.ι Fs i).hom ≫ gsh.hom = pullback.fst g (Ufam i).ι := fun i ↦
    Sheaf.hom_ext_iff.mp (Sigma.ι_comp_desc (fun i ↦ ObjectProperty.homMk
      (pullback.fst g (Ufam i).ι) :
        ∀ i, Fs i ⟶ (⟨N, hN⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u))) i)
  have _ := hcov.2
  have hlocsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) gsh.hom := by
    refine ⟨fun {X} s ↦ ?_⟩
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
        (Sigma.desc fun i ↦ (Ufam i).ι) (g.app (op X) s))
    rintro Z φ ⟨t, ht⟩
    obtain ⟨⟨i⟩, t', rfl⟩ :=
      FunctorToTypes.jointly_surjective' (Discrete.functor fun i ↦ (Ufam i).toFunctor) (op Z) t
    have hdesc : Sigma.ι (fun j ↦ (Ufam j).toFunctor) i ≫ (Sigma.desc fun j ↦ (Ufam j).ι) =
        (Ufam i).ι := Sigma.ι_comp_desc _ i
    have htt : (Ufam i).ι.app (op Z) t' = g.app (op Z) (N.map φ.op s) := by
      rw [NatTrans.naturality_apply g φ.op s, ← ht, ← hdesc]
      rfl
    have hcomm : yonedaEquiv.symm (N.map φ.op s) ≫ g =
        yonedaEquiv.symm t' ≫ (Ufam i).ι := by
      refine yonedaEquiv.injective ?_
      rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact htt.symm
    refine ⟨yonedaEquiv (pullback.lift _ _ hcomm ≫ (Sigma.ι Fs i).hom), ?_⟩
    rw [← yonedaEquiv_comp, Category.assoc, hιdesc i, pullback.lift_fst,
      Equiv.apply_symm_apply]
  refine _root_.AlgebraicGeometry.isAlgebraicSpace_of_open_cover B S hS N hN ι Fs
    (fun i ↦ halg i) (∐ Fs) (Sigma.ι Fs) (coproductIsCoproduct Fs) gsh.hom (fun i ↦ ?_) hlocsurj
    (isAlgebraicSpace_finiteCoproduct B S hS (fun i ↦ pullback g (Ufam i).ι) halg
      (∐ Fs) (Sigma.ι Fs) (coproductIsCoproduct Fs))
  rw [hιdesc i]
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback g (Ufam i).ι).flip (hcov.1 i).2

/-- **The last step of the proof of Stacks 0BGY.** Let `f : V ⟶ W` be an étale morphism of
algebraic spaces over `S` and let `T` be a closed subspace of `W` whose preimage is carried
isomorphically onto `T` by `f`. Let `g : N ⟶ W` be a morphism from an fppf sheaf such that the
projection `N ×_W (W ∖ T) ⟶ W ∖ T` is an isomorphism and the base change `N ×_W V` is isomorphic
to an algebraic space `Y`. Then `N` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_isIso_pullback_snd_of_isAlgebraicSpace_pullback
    {V W Y N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : V ⟶ W) (hf : IsEtale B S hS f)
    (T : Subfunctor W) (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f))
    (g : N ⟶ W)
    (hN : Presheaf.IsSheaf (BigFppfOver.topology B S hS) N)
    (hNW₀ : IsIso (CategoryTheory.Limits.pullback.snd g (openComplement B S hS T).ι))
    (e : CategoryTheory.Limits.pullback g f ≅ Y) :
    IsAlgebraicSpace B S hS N := by
  classical
  obtain ⟨I, hIopen, U, a, q, hqI, hqsurj, hqetale, hcover⟩ :=
    exists_openImage_isZariskiCover_openComplement B S hS
      (V := (⟨V, hV⟩ : AlgebraicSpaces B S hS)) (W := ⟨W, hW⟩)
      (ObjectProperty.homMk f) T hT hfT hf
  have hqI' : q ≫ I.ι = a ≫ f := hqI
  have hIalg : IsAlgebraicSpace B S hS I.toFunctor := hIopen.1
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hgf : IsAlgebraicSpace B S hS (pullback g f) := isAlgebraicSpace_of_iso B S hS e.symm hY
  have hNU : IsAlgebraicSpace B S hS (pullback g (a ≫ f)) :=
    isAlgebraicSpace_of_iso B S hS (pullbackLeftPullbackSndIso g f a)
      (isAlgebraicSpace_pullback B S hS (pullback.snd g f) a hgf hUalg hV)
  have hX : IsAlgebraicSpace B S hS (pullback (pullback.snd g I.ι) q) :=
    isAlgebraicSpace_of_iso B S hS
      ((pullbackLeftPullbackSndIso g I.ι q).trans (pullback.congrHom rfl hqI')).symm hNU
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS q :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hUalg hIalg q
  have hqS : HasProperty B S hS (surjectiveMorphismProperty B S hS) q hqrep := fun U' ξ ↦
    isSurjective_pullback_fst B S hS (isAlgebraicSpace_yoneda B S hS U') hIalg hUalg ξ q hqsurj
  have hqE : HasProperty B S hS (etaleMorphisms B S hS) q hqrep := fun U' ξ ↦
    isEtale_pullback_fst B S hS (isAlgebraicSpace_yoneda B S hS U') hIalg hUalg ξ q hqetale
  have hsq : IsPullback (pullback.snd (pullback.snd g I.ι) q)
      (pullback.fst (pullback.snd g I.ι) q) q (pullback.snd g I.ι) :=
    (IsPullback.of_hasPullback (pullback.snd g I.ι) q).flip
  have _ : (etaleMorphisms B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hPI : IsAlgebraicSpace B S hS (pullback g I.ι) :=
    isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
      (Presheaf.isSheaf_pullback _ g I.ι hN hIalg.isSheaf hW.isSheaf) hX _
      (IsRepresentableByAlgebraicSpaces.of_isPullback hsq hqrep)
      (HasProperty.of_isPullback hsq hqrep hqS) (HasProperty.of_isPullback hsq hqrep hqE)
  have _ := hNW₀
  have hPW₀ : IsAlgebraicSpace B S hS (pullback g (openComplement B S hS T).ι) :=
    isAlgebraicSpace_of_iso B S hS
      (asIso (pullback.snd g (openComplement B S hS T).ι)).symm
      (isOpenSubspace_openComplement B S hS hW T hT).1
  refine isAlgebraicSpace_of_isZariskiCover_pullback B S hS g hN _ hcover ?_
  rintro ⟨b⟩
  cases b
  · exact hPI
  · exact hPW₀

end AlgebraicGeometry.Space

end
