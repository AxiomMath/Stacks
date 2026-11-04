module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckExistenceII

/-!
# Completion on a closed subscheme, from the essential image on the ambient scheme

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒥 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals and
let `i : Z = V(𝒥) ⟶ X` be the closed immersion cut out by `𝒥`. Granted

* full faithfulness of the completion functor `Coh(𝒪_X) ⥤ Coh(X, ℐ)` of [Stacks, Tag 0880], and
* that every object of `Coh(X, ℐ)` killed by `𝒥` is in the essential image of that functor —
  that is, `𝒥 ∈ Ξ` for the family `Ξ` of the proof of [Stacks, Tag 088C],

the completion functor `Coh(𝒪_Z) ⥤ Coh(Z, ℐ 𝒪_Z)` on the closed subscheme is an **equivalence**.
Applied to the closed subschemes `V(𝒦 ᵉ⁺¹)`, this gives hypothesis (1) of [Stacks, Tag 088A].

## Main definitions

* `Stacks.Coherent.coherentPushforwardClosed` — direct image as a functor
  `Coh(𝒪_Z) ⥤ Coh(𝒪_X)`.
* `Stacks.Coherent.completionPushforwardNatIso` — **direct image commutes with completion**, as
  an isomorphism of functors `Coh(𝒪_Z) ⥤ Coh(X, ℐ)`.

## Main results

* `Stacks.Coherent.completionProjection_comp_bijective` — precomposition with the projection onto
  a term of the completion is bijective on maps into a module killed by the corresponding power.
* `Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion_eq_bot` — if the completion functor is
  fully faithful and every term of `M ^∧_ℐ` is killed by `𝒥`, then `M` is killed by `𝒥`.
* `Stacks.Coherent.fullyFaithful_completionFunctor_comap` — completion on `Z` along `ℐ 𝒪_Z` is
  fully faithful as soon as completion on `X` along `ℐ` is.
* `Stacks.Coherent.isEquivalence_completionFunctor_subscheme_of_essImage` — completion on `V(𝒥)`
  is an equivalence.
* `Stacks.Coherent.isEquivalence_completionFunctor_pow_of_essImage` — the same at every power
  `𝒦 ᵉ⁺¹`, which is hypothesis (1) of [Stacks, Tag 088A].
* `Stacks.Coherent.essImage_completionFunctor_of_essImage_annihilated` — [Stacks, Tag 088A] with
  hypothesis (1) traded for membership of the powers of `𝒦` in `Ξ`.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-! ### Precomposition with a completion projection -/

/-- **Precomposition with the projection onto the `n`-th term of the completion is bijective** on
maps into a module annihilated by `ℐ ⁿ⁺¹`. -/
public theorem completionProjection_comp_bijective {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData)
    (A : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) (n : ℕ)
    {N : Y.Modules} (hN : idealPowerMultiple I (n + 1) N = ⊥) :
    Function.Bijective (fun g : ((completionFunctor Y I).obj A).obj.obj (op n) ⟶ N =>
      completionProjection Y I A n ≫ g) := by
  have h1 : Function.Bijective (fun g : idealPowerQuotient I (n + 1) A.obj ⟶ N =>
      cokernel.π (C := Y.Modules) (idealPowerMultiple I (n + 1) A.obj).ι ≫ g) :=
    quotientProjection_comp_bijective I (n + 1) hN
  have h2 : Function.Bijective (fun g : ((completionFunctor Y I).obj A).obj.obj (op n) ⟶ N =>
      eqToHom (completionFunctor_obj Y I A n).symm ≫ g) := by
    refine ⟨fun a b hab => (cancel_epi (eqToHom (completionFunctor_obj Y I A n).symm)).1 hab,
      fun k => ⟨eqToHom (completionFunctor_obj Y I A n) ≫ k, ?_⟩⟩
    exact ((Category.assoc (obj := Y.Modules) _ _ _).symm.trans
      (congrArg (fun z => z ≫ k) ((eqToHom_trans _ _).trans (eqToHom_refl _ rfl)))).trans
      (Category.id_comp (obj := Y.Modules) k)
  have heq : (fun g : ((completionFunctor Y I).obj A).obj.obj (op n) ⟶ N =>
        completionProjection Y I A n ≫ g) =
      (fun k : idealPowerQuotient I (n + 1) A.obj ⟶ N =>
          cokernel.π (C := Y.Modules) (idealPowerMultiple I (n + 1) A.obj).ι ≫ k) ∘
        (fun g : ((completionFunctor Y I).obj A).obj.obj (op n) ⟶ N =>
          eqToHom (completionFunctor_obj Y I A n).symm ≫ g) :=
    funext fun g => Category.assoc (obj := Y.Modules) _ _ _
  rw [heq]
  exact h1.comp h2

/-! ### Annihilation descends from the completion -/

/-- **Annihilation of the completion is annihilation of the module**, granted full faithfulness
of the completion functor. If every term of `M ^∧_ℐ` is killed by `𝒥`, then so is `M`. -/
public theorem idealPowerMultiple_eq_bot_of_completion_eq_bot {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I J : X.IdealSheafData)
    (hff : (completionFunctor X I).FullyFaithful)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (h : ∀ n : ℕ,
      idealPowerMultiple J 1 (((completionFunctor X I).obj M).obj.obj (op n)) = ⊥) :
    idealPowerMultiple J 1 M.obj = ⊥ := by
  have hQ : coherentAnnihilatedBy J 1 (idealPowerQuotient J 1 M.obj) :=
    coherentAnnihilatedBy_idealPowerQuotient J 0 M.obj M.property
  let Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨idealPowerQuotient J 1 M.obj, hQ.1⟩
  let q : M ⟶ Q := ObjectProperty.homMk
    (cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M.obj).ι)
  have hqepi : Epi (C := X.Modules) q.hom := epi_cokernel_π_submodule_ι _
  have hcomp : ∀ n : ℕ, IsIso (((completionFunctor X I).map q).hom.app (op n)) := by
    intro n
    have hθ := completionFunctor_map_quotient X I q n
    obtain ⟨d, hd⟩ := (quotientProjection_comp_bijective J 1 (h n)).2
      (completionProjection X I M n)
    change cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M.obj).ι ≫ d =
      completionProjection X I M n at hd
    obtain ⟨c, hc⟩ := (completionProjection_comp_bijective I Q n
      (((completionFunctor X I).obj M).property.2.1 n)).2 d
    change completionProjection X I Q n ≫ c = d at hc
    have hdθ : d ≫ ((completionFunctor X I).map q).hom.app (op n) =
        completionProjection X I Q n := by
      refine hqepi.left_cancellation _ _ ?_
      exact ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        (congrArg (fun z => z ≫ ((completionFunctor X I).map q).hom.app (op n)) hd)).trans hθ
    refine ⟨c, ?_, ?_⟩
    · refine (Stacks.Algebraization.epi_completionProjection X I M n).left_cancellation _ _ ?_
      refine Eq.trans ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ c) hθ).trans (Category.assoc (obj := X.Modules) _ _ _))) ?_
      refine Eq.trans (congrArg (fun z => q.hom ≫ z) hc) ?_
      exact hd.trans (Category.comp_id (obj := X.Modules) _).symm
    · refine (Stacks.Algebraization.epi_completionProjection X I Q n).left_cancellation _ _ ?_
      refine Eq.trans ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        (congrArg (fun z => z ≫ ((completionFunctor X I).map q).hom.app (op n)) hc)) ?_
      exact hdθ.trans (Category.comp_id (obj := X.Modules) _).symm
  let hcomp' : ∀ n : ℕᵒᵖ, IsIso (((completionFunctor X I).map q).hom.app n) :=
    fun n => hcomp n.unop
  have : IsIso ((completionFunctor X I).map q).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((completionFunctor X I).map q) :=
    ⟨ObjectProperty.homMk (inv ((completionFunctor X I).map q).hom),
      ObjectProperty.hom_ext _ (IsIso.hom_inv_id _),
      ObjectProperty.hom_ext _ (IsIso.inv_hom_id _)⟩
  have hqiso : IsIso q := hff.isIso_of_isIso_map q
  have hqinv : cokernel.π (C := X.Modules) (idealPowerMultiple J 1 M.obj).ι ≫ (inv q).hom =
      𝟙 M.obj := congrArg (fun k : M ⟶ M => k.hom) (IsIso.hom_inv_id q)
  have hz := cokernel.condition (C := X.Modules) (idealPowerMultiple J 1 M.obj).ι
  refine (submodule_ι_eq_zero_iff _).1 ?_
  exact (Category.comp_id (obj := X.Modules) _).symm.trans
    ((congrArg (fun z => (idealPowerMultiple J 1 M.obj).ι ≫ z) hqinv.symm).trans
      ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (inv q).hom) hz).trans (zero_comp (C := X.Modules)))))

/-! ### Direct image on coherent modules, along a closed immersion -/

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The direct image along a closed immersion of a coherent module, as a coherent module. -/
public theorem isCoherent_pushforward_obj [IsLocallyNoetherian X]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ((Scheme.Modules.pushforward i).obj G.obj).IsCoherent :=
  have _ : G.obj.IsCoherent := G.property
  isCoherent_pushforward_of_isClosedImmersion i G.obj

/-- **Direct image along a closed immersion as a functor `Coh(𝒪_Z) ⥤ Coh(𝒪_X)`.** -/
public def coherentPushforwardClosed [IsLocallyNoetherian X] :
    AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf ⥤
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun N : _root_.SheafOfModules Z.ringCatSheaf => N.IsCoherent) ⋙
      Scheme.Modules.pushforward i)
    (isCoherent_pushforward_obj i)

/-- The underlying module of the direct image is the direct image of the underlying module. -/
public theorem coherentPushforwardClosed_obj_obj [IsLocallyNoetherian X]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    ((coherentPushforwardClosed i).obj G).obj =
      (Scheme.Modules.pushforward i).obj G.obj := rfl

/-- Direct image on coherent modules acts on morphisms by direct image. -/
public theorem coherentPushforwardClosed_map_hom [IsLocallyNoetherian X]
    {G G' : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf} (f : G ⟶ G') :
    ((coherentPushforwardClosed i).map f).hom = (Scheme.Modules.pushforward i).map f.hom := rfl

/-- **Direct image along a closed immersion is fully faithful on coherent modules.** -/
public def fullyFaithfulCoherentPushforwardClosed [IsLocallyNoetherian X] :
    (coherentPushforwardClosed i).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := ObjectProperty.ι (fun N : _root_.SheafOfModules X.ringCatSheaf => N.IsCoherent))
    (((ObjectProperty.fullyFaithfulι
        (fun N : _root_.SheafOfModules Z.ringCatSheaf => N.IsCoherent)).comp
      (Stacks.ClosedImmersion.fullyFaithfulPushforward i)).ofIso
        (ObjectProperty.liftCompιIso _ _ _).symm)

/-- **Termwise direct image along a closed immersion is fully faithful on coherent adic
systems.** -/
public def fullyFaithfulCoherentAdicPushforwardClosed [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (coherentAdicPushforwardClosed i I).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι (IsCoherentAdicSystem I))
    (((ObjectProperty.fullyFaithfulι (IsCoherentAdicSystem (I.comap i))).comp
      ((Stacks.ClosedImmersion.fullyFaithfulPushforward i).whiskeringRight ℕᵒᵖ)).ofIso
        (ObjectProperty.liftCompιIso _ _ _).symm)

/-! ### Direct image commutes with completion, naturally -/

/-- **Direct image along a closed immersion commutes with completion**, as an isomorphism of
functors `Coh(𝒪_Z) ⥤ Coh(X, ℐ)`. -/
public def completionPushforwardNatIso [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    coherentPushforwardClosed i ⋙ completionFunctor X I ≅
      completionFunctor Z (I.comap i) ⋙ coherentAdicPushforwardClosed i I := by
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  refine NatIso.ofComponents (fun G => ObjectProperty.isoMk (IsCoherentAdicSystem I)
    (completionPushforwardIso i I G (isCoherent_pushforward_obj i G))) ?_
  intro G G' f
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  refine (Stacks.Algebraization.epi_completionProjection X I
    ((coherentPushforwardClosed i).obj G) n.unop).left_cancellation _ _ ?_
  have hqX := completionFunctor_map_quotient X I ((coherentPushforwardClosed i).map f) n.unop
  have hG := completionPushforwardIso_completionProjection i I G
    (isCoherent_pushforward_obj i G) n.unop
  have hG' := completionPushforwardIso_completionProjection i I G'
    (isCoherent_pushforward_obj i G') n.unop
  have hZ := completionFunctor_map_quotient Z (I.comap i) f n.unop
  have left : completionProjection X I ((coherentPushforwardClosed i).obj G) n.unop ≫
      (((coherentPushforwardClosed i ⋙ completionFunctor X I).map f).hom.app n ≫
        (completionPushforwardIso i I G' (isCoherent_pushforward_obj i G')).hom.app n) =
      (Scheme.Modules.pushforward i).map
        (f.hom ≫ completionProjection Z (I.comap i) G' n.unop) := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun z => z ≫ (completionPushforwardIso i I G'
        (isCoherent_pushforward_obj i G')).hom.app n) hqX) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg
      (fun z => ((coherentPushforwardClosed i).map f).hom ≫ z) hG') ?_
    exact ((Scheme.Modules.pushforward i).map_comp _ _).symm
  have right : completionProjection X I ((coherentPushforwardClosed i).obj G) n.unop ≫
      ((completionPushforwardIso i I G (isCoherent_pushforward_obj i G)).hom.app n ≫
        ((completionFunctor Z (I.comap i) ⋙ coherentAdicPushforwardClosed i I).map f).hom.app n) =
      (Scheme.Modules.pushforward i).map
        (f.hom ≫ completionProjection Z (I.comap i) G' n.unop) := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      ((completionFunctor Z (I.comap i) ⋙
        coherentAdicPushforwardClosed i I).map f).hom.app n) hG) ?_
    refine Eq.trans ((Scheme.Modules.pushforward i).map_comp _ _).symm ?_
    exact congrArg (Scheme.Modules.pushforward i).map hZ
  exact left.trans right.symm

end

/-! ### Completion on the closed subscheme -/

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I J : X.IdealSheafData)

/-- **Completion on a closed subscheme is fully faithful** as soon as completion on the ambient
scheme is. -/
public def fullyFaithful_completionFunctor_comap
    (hff : (completionFunctor X I).FullyFaithful) :
    letI : IsLocallyNoetherian J.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion J.subschemeι
    (completionFunctor J.subscheme (I.comap J.subschemeι)).FullyFaithful :=
  letI : IsLocallyNoetherian J.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion J.subschemeι
  letI : (coherentAdicPushforwardClosed J.subschemeι I).Faithful :=
    (fullyFaithfulCoherentAdicPushforwardClosed J.subschemeι I).faithful
  Functor.FullyFaithful.ofCompFaithful
    (G := coherentAdicPushforwardClosed J.subschemeι I)
    (((fullyFaithfulCoherentPushforwardClosed J.subschemeι).comp hff).ofIso
      (completionPushforwardNatIso J.subschemeι I))

/-- Let `X` be a locally Noetherian scheme and `ℐ, 𝒥 ⊆ 𝒪_X` quasi-coherent
sheaves of ideals. Suppose the completion functor `Coh(𝒪_X) ⥤ Coh(X, ℐ)` of [Stacks, Tag 0880]
is fully faithful, and that every object of `Coh(X, ℐ)` killed by `𝒥` is in its essential image.
Then the completion functor `Coh(𝒪_Z) ⥤ Coh(Z, ℐ 𝒪_Z)` of the closed subscheme `Z = V(𝒥)` is an
**equivalence**. -/
public theorem isEquivalence_completionFunctor_subscheme_of_essImage
    (hff : (completionFunctor X I).FullyFaithful)
    (hJ : ∀ 𝓕 : CoherentAdicSystems I, IsSystemAnnihilatedBy J 𝓕.obj →
      (completionFunctor X I).essImage 𝓕) :
    letI : IsLocallyNoetherian J.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion J.subschemeι
    (completionFunctor J.subscheme (I.comap J.subschemeι)).IsEquivalence := by
  let : IsLocallyNoetherian J.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion J.subschemeι
  set i : J.subscheme ⟶ X := J.subschemeι
  have hkerJ : i.ker = J := Scheme.IdealSheafData.ker_subschemeι J
  let hffZ := fullyFaithful_completionFunctor_comap I J hff
  let : (completionFunctor J.subscheme (I.comap i)).Full := hffZ.full
  let : (completionFunctor J.subscheme (I.comap i)).Faithful := hffZ.faithful
  let := (fullyFaithfulCoherentAdicPushforwardClosed i I).full
  let := (fullyFaithfulCoherentAdicPushforwardClosed i I).faithful
  let : (completionFunctor J.subscheme (I.comap i)).EssSurj := by
    refine ⟨fun N => ?_⟩
    have hann : IsSystemAnnihilatedBy J
        ((coherentAdicPushforwardClosed i I).obj N).obj := by
      intro n
      have h := idealPowerMultiple_ker_pushforward_eq_bot i (N.obj.obj (op n))
      rwa [hkerJ] at h
    obtain ⟨M, ⟨e⟩⟩ := hJ ((coherentAdicPushforwardClosed i I).obj N) hann
    have hterm : ∀ n : ℕ,
        idealPowerMultiple J 1 (((completionFunctor X I).obj M).obj.obj (op n)) = ⊥ :=
      fun n => idealPowerMultiple_eq_bot_of_iso J
        (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso e).app (op n)) 1 (hann n)
    have hM : idealPowerMultiple i.ker 1 M.obj = ⊥ := by
      rw [hkerJ]
      exact idealPowerMultiple_eq_bot_of_completion_eq_bot I J hff M hterm
    refine ⟨(coherentPullback i).obj M, ?_⟩
    refine ⟨(coherentAdicPushforwardClosed i I).preimageIso
      ((ObjectProperty.isoMk (IsCoherentAdicSystem I)
        (completionAnnihilatedPushforwardIso i I M hM)).symm ≪≫ e)⟩
  exact { }

end

/-! ### Hypothesis (1) of Tag 088A -/

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **Hypothesis (1) of [Stacks, Tag 088A], from membership of the powers of `𝒦` in `Ξ`.** If the
completion functor along `ℐ` on `X` is fully faithful and, for every `e`, every object of
`Coh(X, ℐ)` killed by `𝒦 ᵉ⁺¹` is in its essential image, then for every `e` the completion
functor of the closed subscheme `V(𝒦 ᵉ⁺¹)` along the inverse image of `ℐ` is an equivalence. -/
public theorem isEquivalence_completionFunctor_pow_of_essImage (I K : X.IdealSheafData)
    (hff : (completionFunctor X I).FullyFaithful)
    (hK : ∀ e : ℕ, ∀ 𝓕 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy (K ^ (e + 1)) 𝓕.obj → (completionFunctor X I).essImage 𝓕) :
    ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence :=
  fun e => isEquivalence_completionFunctor_subscheme_of_essImage I (K ^ (e + 1)) hff (hK e)

/-- **[Stacks, Tag 088A] with hypothesis (1) traded for membership of the powers of `𝒦` in the
family `Ξ` of [Stacks, Tag 088C].** Let `X` be a Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be
quasi-coherent sheaves of ideals, and let `(F_n)` be an object of `Coh(X, ℐ)` admitting a
morphism `α : (F_n) ⟶ H ^∧_ℐ` from a coherent `𝒪_X`-module `H` whose levelwise kernels and
cokernels are annihilated by a power of `𝒦` — hypothesis (2). If the completion functor is fully
faithful and every object of `Coh(X, ℐ)` killed by a positive power of `𝒦` is in its essential
image, then `(F_n)` is in the essential image too. -/
public theorem essImage_completionFunctor_of_essImage_annihilated [IsNoetherian X]
    (I K : X.IdealSheafData) (Fsys : CoherentAdicSystems I)
    (hff : (completionFunctor X I).FullyFaithful)
    (hK : ∀ e : ℕ, ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy (K ^ (e + 1)) 𝓖.obj → (completionFunctor X I).essImage 𝓖)
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (α : Fsys ⟶ (completionFunctor X I).obj H)
    (hα : IsKernelCokernelAnnihilatedByPower K α.hom) :
    (completionFunctor X I).essImage Fsys :=
  essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower I K Fsys
    (isEquivalence_completionFunctor_pow_of_essImage I K hff hK) H α hα

end

end Stacks.Coherent

end
