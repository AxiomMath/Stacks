module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionAdicSystem

/-!
# Hypothesis (1) of Tag 088A, read on the ambient scheme

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals, let
`e ≥ 1` and let `X_e ⊆ X` be the closed subscheme cut out by `𝒦 ᵉ`, with `ℐ_e = ℐ 𝒪_{X_e}`.
Hypothesis (1) of [Stacks, Tag 088A] is that the completion functor of [Stacks, Tag 0880]

`Coh(𝒪_{X_e}) ⟶ Coh(X_e, ℐ_e)`

is an equivalence. The source uses it twice, and both times through the closed-immersion
equivalence of [Stacks, Tag 087T], which identifies `Coh(𝒪_{X_e})` with the coherent
`𝒪_X`-modules annihilated by `𝒦 ᵉ` and `Coh(X_e, ℐ_e)` with the full subcategory of `Coh(X, ℐ)`
they cut out. This file performs that transport: it turns hypothesis (1) into two statements
about `X` itself, essential surjectivity and full faithfulness of the completion functor of `X`
restricted to the `𝒦 ᵉ`-annihilated coherent modules.

## Main results

* `Stacks.Coherent.exists_coherent_completion_iso_of_annihilated` — **essential surjectivity**: a
  coherent adic system along `ℐ` all of whose terms are annihilated by `𝒦 ᵉ` is the completion of
  a coherent `𝒪_X`-module annihilated by `𝒦 ᵉ`.
* `Stacks.Coherent.bijective_completion_map_of_annihilated` — **full faithfulness**: for coherent
  `𝒪_X`-modules annihilated by `𝒦 ᵉ`, the completion functor is bijective on morphisms.
* `Stacks.Coherent.bijective_completion_map_pushforward` — the same for a direct image along an
  arbitrary closed immersion whose completion functor upstairs is an equivalence; this is the
  form the proof of full faithfulness takes before the two modules are recognized as direct
  images.
* `Stacks.Coherent.bijective_completion_map_of_iso` — bijectivity of the completion map is
  invariant under isomorphism of the two modules.

## Implementation notes

Essential surjectivity is a chain: the system is a termwise direct image
(`Stacks.Coherent.exists_system_pushforward_iso`), the system upstairs is a coherent adic system
along `ℐ_e` (`Stacks.Coherent.isCoherentAdicSystem_of_pushforward`), hypothesis (1) algebraizes
it on `X_e`, and the comparison of the two completions
(`Stacks.Algebraization.pushforwardCompletionIso`) brings the result back to `X`.

Full faithfulness is the commuting square

```
Hom(G, G')                  --completion on X_e-->  Hom(G ^∧, G' ^∧)
   |  i_*                                              |  i_* and the comparison
Hom(i_* G, i_* G')          --completion on X  -->  Hom((i_* G) ^∧, (i_* G') ^∧)
```

whose top edge is bijective by hypothesis (1), whose left edge is bijective by [Stacks, Tag
08KS] and whose right edge is bijective because termwise direct image is
(`Stacks.Coherent.bijective_whiskerRight_pushforward`) and the comparison is an isomorphism. That
the square commutes is `Stacks.Algebraization.pushforwardCompletionIso_naturality`. The
conclusion is `Stacks.Coherent.bijective_iff_of_commSquare`.

`AlgebraicGeometry.Scheme.IdealSheafData.subscheme` of a locally Noetherian scheme is locally
Noetherian, which the completion functor on `X_e` needs in order to be written down at all; the
instance is supplied locally here, since it is not one instance search can find for an arbitrary
scheme.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization Stacks.AlgebraicGeometry.Tag087TCoherentImage

/-! ### Invariance of the completion map under isomorphism -/

/-- Bijectivity of the completion map on morphisms is invariant under isomorphism of the source
and of the target, by functoriality of the completion functor. -/
public theorem bijective_completion_map_of_iso {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData)
    {M N M' N' : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf}
    (eM : M ≅ M') (eN : N ≅ N')
    (h : Function.Bijective (fun f : M' ⟶ N' => ((completionFunctor Y I).map f).hom)) :
    Function.Bijective (fun f : M ⟶ N => ((completionFunctor Y I).map f).hom) := by
  refine (bijective_iff_of_commSquare _ _
    (fun f : M ⟶ N => eM.inv ≫ f ≫ eN.hom)
    (fun α : ((completionFunctor Y I).obj M).obj ⟶ ((completionFunctor Y I).obj N).obj =>
      ((completionFunctor Y I).map eM.inv).hom ≫ α ≫ ((completionFunctor Y I).map eN.hom).hom)
    (Iso.homCongr eM eN).bijective
    (Iso.homCongr ((ObjectProperty.ι _).mapIso ((completionFunctor Y I).mapIso eM))
      ((ObjectProperty.ι _).mapIso ((completionFunctor Y I).mapIso eN))).bijective
    fun f => ?_).mpr h
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-! ### Full faithfulness for a direct image along a closed immersion -/

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- **The completion functor is bijective on morphisms between direct images**, as soon as the
completion functor on `Z` is an equivalence.

The square of the module docstring, with its three bijective edges. -/
public theorem bijective_completion_map_pushforward (I : X.IdealSheafData)
    (h1 : (completionFunctor Z (I.comap i)).IsEquivalence)
    (G G' : AlgebraicGeometry.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    Function.Bijective (fun f : pushforwardCoherentObj i G ⟶ pushforwardCoherentObj i G' =>
      ((completionFunctor X I).map f).hom) := by
  have := h1
  have ffZ : (ObjectProperty.ι
      (fun M : Z.Modules => _root_.SheafOfModules.IsCoherent M)).FullyFaithful :=
    ObjectProperty.fullyFaithfulι _
  have ffX : (ObjectProperty.ι
      (fun M : X.Modules => _root_.SheafOfModules.IsCoherent M)).FullyFaithful :=
    ObjectProperty.fullyFaithfulι _
  have ffsys : (ObjectProperty.ι (IsCoherentAdicSystem (I.comap i))).FullyFaithful :=
    ObjectProperty.fullyFaithfulι _
  have ffpf := Stacks.ClosedImmersion.fullyFaithfulPushforward i
  -- the completion map on `Z`
  have hTZ : Function.Bijective
      (fun f : G ⟶ G' => ((completionFunctor Z (I.comap i)).map f).hom) :=
    Function.Bijective.comp
      (ffsys.map_bijective ((completionFunctor Z (I.comap i)).obj G)
        ((completionFunctor Z (I.comap i)).obj G'))
      ((Functor.FullyFaithful.ofFullyFaithful (completionFunctor Z (I.comap i))).map_bijective
        G G')
  -- direct image on morphisms of coherent modules
  have hL : Function.Bijective
      (fun f : G ⟶ G' => pushforwardCoherentMap i f) := by
    refine ⟨fun f f' hff => ObjectProperty.hom_ext _ (ffpf.map_injective ?_), fun g => ?_⟩
    · exact congrArg
        (fun k : pushforwardCoherentObj i G ⟶ pushforwardCoherentObj i G' => k.hom) hff
    · exact ⟨ObjectProperty.homMk (ffpf.preimage g.hom),
        ObjectProperty.hom_ext _ (ffpf.map_preimage g.hom)⟩
  -- direct image on morphisms of inverse systems, conjugated by the comparison
  have hR : Function.Bijective
      (fun α : ((completionFunctor Z (I.comap i)).obj G).obj ⟶
          ((completionFunctor Z (I.comap i)).obj G').obj =>
        (pushforwardCompletionIso i I G).hom ≫
          Functor.whiskerRight α (Scheme.Modules.pushforward i) ≫
            (pushforwardCompletionIso i I G').inv) := by
    refine ⟨fun α β hab => ?_, fun γ => ?_⟩
    · simp only [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] at hab
      exact (bijective_whiskerRight_pushforward i _ _).1 hab
    · obtain ⟨α, hα⟩ := (bijective_whiskerRight_pushforward i _ _).2
        ((pushforwardCompletionIso i I G).inv ≫ γ ≫ (pushforwardCompletionIso i I G').hom)
      have hα' : Functor.whiskerRight α (Scheme.Modules.pushforward i) =
          (pushforwardCompletionIso i I G).inv ≫ γ ≫
            (pushforwardCompletionIso i I G').hom := hα
      refine ⟨α, ?_⟩
      change (pushforwardCompletionIso i I G).hom ≫
        Functor.whiskerRight α (Scheme.Modules.pushforward i) ≫
          (pushforwardCompletionIso i I G').inv = γ
      rw [hα']
      simp
  refine (bijective_iff_of_commSquare _ _ _ _ hL hR fun f => ?_).mp hTZ
  refine NatTrans.ext (funext fun n => ?_)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (pushforwardCompletionIso i I G').inv.app n)
        (pushforwardCompletionIso_naturality i I f n.unop).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k =>
              ((completionFunctor X I).map (pushforwardCoherentMap i f)).hom.app n ≫ k)
            (Iso.hom_inv_id_app (pushforwardCompletionIso i I G') n)).trans
          (Category.comp_id _))))

end ClosedImmersion

/-! ### Hypothesis (1) transported to the ambient scheme -/

section Subscheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The closed subscheme cut out by a quasi-coherent ideal sheaf on a locally Noetherian scheme
is locally Noetherian. -/
local instance isLocallyNoetherian_subscheme (J : X.IdealSheafData) :
    IsLocallyNoetherian J.subscheme :=
  isLocallyNoetherian_of_isClosedImmersion J.subschemeι

/-- **Essential surjectivity, transported.** Assume hypothesis (1) of [Stacks, Tag 088A] at level
`e`. Then a coherent adic system along `ℐ` all of whose terms are annihilated by `𝒦 ᵉ` is the
completion of a coherent `𝒪_X`-module annihilated by `𝒦 ᵉ`. -/
public theorem exists_coherent_completion_iso_of_annihilated (I K : X.IdealSheafData) (e : ℕ)
    (h1 : (completionFunctor (K ^ e).subscheme (I.comap (K ^ e).subschemeι)).IsEquivalence)
    (P : ℕᵒᵖ ⥤ X.Modules) (hP : IsCoherentAdicSystem I P)
    (hann : ∀ n : ℕ, idealPowerMultiple K e (P.obj (op n)) = ⊥) :
    ∃ M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      idealPowerMultiple K e M.obj = ⊥ ∧
        Nonempty (((completionFunctor X I).obj M).obj ≅ P) := by
  have := h1
  obtain ⟨Q, hQcoh, ⟨eQ⟩⟩ := exists_system_pushforward_iso (K ^ e).subschemeι P
    (fun n => hP.1 n.unop)
    (fun n => (annihilatedByKer_subschemeι_pow_iff K e (P.obj n)).mpr (hann n.unop))
  have hQsys : IsCoherentAdicSystem (I.comap (K ^ e).subschemeι) Q :=
    isCoherentAdicSystem_of_pushforward (K ^ e).subschemeι I Q hQcoh
      (isCoherentAdicSystem_of_iso I eQ.symm hP)
  obtain ⟨G, ⟨eG⟩⟩ := Functor.EssSurj.mem_essImage
    (F := completionFunctor (K ^ e).subscheme (I.comap (K ^ e).subschemeι))
    (⟨Q, hQsys⟩ : CoherentAdicSystems (I.comap (K ^ e).subschemeι))
  refine ⟨pushforwardCoherentObj (K ^ e).subschemeι G, ?_, ⟨?_⟩⟩
  · exact (annihilatedByKer_subschemeι_pow_iff K e _).mp
      (annihilatedByKer_pushforward (K ^ e).subschemeι G.obj)
  · exact (pushforwardCompletionIso (K ^ e).subschemeι I G).trans
      ((Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso eG)
        (Scheme.Modules.pushforward (K ^ e).subschemeι)).trans eQ)

/-- **Full faithfulness, transported.** Assume hypothesis (1) of [Stacks, Tag 088A] at level `e`.
Then for coherent `𝒪_X`-modules annihilated by `𝒦 ᵉ` the completion functor along `ℐ` is
bijective on morphisms. -/
public theorem bijective_completion_map_of_annihilated (I K : X.IdealSheafData) (e : ℕ)
    (h1 : (completionFunctor (K ^ e).subscheme (I.comap (K ^ e).subschemeι)).IsEquivalence)
    (M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple K e M.obj = ⊥) (hN : idealPowerMultiple K e N.obj = ⊥) :
    Function.Bijective (fun f : M ⟶ N => ((completionFunctor X I).map f).hom) := by
  have key : ∀ M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      idealPowerMultiple K e M.obj = ⊥ → ∃ G, Nonempty (M ≅ pushforwardCoherentObj
        (K ^ e).subschemeι G) := fun M hM => by
    obtain ⟨G, hG, ⟨eM⟩⟩ :=
      have := M.property
      exists_isCoherent_pushforward_iso (K ^ e).subschemeι M.obj
        ((annihilatedByKer_subschemeι_pow_iff K e M.obj).mpr hM)
    exact ⟨⟨G, hG⟩, ⟨(ObjectProperty.isoMk _ eM).symm⟩⟩
  obtain ⟨G, ⟨eM⟩⟩ := key M hM
  obtain ⟨G', ⟨eN⟩⟩ := key N hN
  exact bijective_completion_map_of_iso I eM eN
    (bijective_completion_map_pushforward (K ^ e).subschemeι I h1 G G')

end Subscheme

end Stacks.Coherent

end
