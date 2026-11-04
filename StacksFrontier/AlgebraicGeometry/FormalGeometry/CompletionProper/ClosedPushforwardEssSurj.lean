module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedSubschemeEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image of coherent adic systems along a closed immersion is an equivalence onto the
annihilated part

Let `i : Z ⟶ X` be a closed immersion into a locally Noetherian scheme, let `ℐ ⊆ 𝒪_X` be a
quasi-coherent sheaf of ideals and let `ℐ_Z = ℐ 𝒪_Z` be its inverse image. Termwise direct image
is a functor

  `i_* : Coh(Z, ℐ_Z) ⥤ Coh(X, ℐ)`

(`Stacks.Coherent.coherentAdicPushforwardClosed`), and it is fully faithful
(`Stacks.Coherent.fullyFaithfulCoherentAdicPushforwardClosed`). It is essentially surjective onto
the systems killed by the ideal sheaf `ker(i)` cutting out `Z`, so that

  `i_* : Coh(Z, ℐ_Z) ≌ { (ℱ_n) ∈ Coh(X, ℐ) : ker(i) ℱ_n = 0 for all n }`

is an equivalence of categories. This is the adic-system analogue of the correspondence of
[Stacks, Tag 087T] between coherent `𝒪_Z`-modules and coherent `𝒪_X`-modules killed by `ker(i)`.

## Main definitions

* `Stacks.Coherent.coherentAdicSystemAnnihilatedByKer` — the coherent adic systems along `ℐ`
  killed by the ideal sheaf cutting out `Z`, as a property of objects of `Coh(X, ℐ)`.
* `Stacks.Coherent.coherentAdicPushforwardKer` — termwise direct image as a functor
  `Coh(Z, ℐ_Z) ⥤ { (ℱ_n) ∈ Coh(X, ℐ) : ker(i) ℱ_n = 0 }`.
* `Stacks.Coherent.coherentAdicPushforwardKerEquivalence` — **that functor is an equivalence.**

## Main results

* `Stacks.Coherent.idealPowerMultiple_comap_eq_bot_of_pushforward_eq_bot` — the converse of
  `Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot`: annihilation by a power of `ℐ`
  descends from a direct image to the module it is the direct image of.
* `Stacks.Coherent.isCoherentAdicSystem_comap_of_pushforward` — **termwise direct image along a
  closed immersion detects coherent adic systems.**
* `Stacks.Coherent.essImage_coherentAdicPushforwardClosed_of_annihilated` — **essential
  surjectivity**: a coherent adic system along `ℐ` all of whose terms are killed by `ker(i)` is
  the termwise direct image of a coherent adic system along `ℐ_Z`.
* `Stacks.Coherent.essImage_coherentAdicPushforwardClosed_subscheme` — the same for the closed
  subscheme `V(𝒦)` cut out by an ideal sheaf `𝒦` of `X`.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-! ### Annihilation descends through the direct image -/

/-- **Annihilation by a power of `ℐ` descends from a direct image.** If `ℐ ⁿ (i_* G)` vanishes
then so does `ℐ_Z ⁿ G`, where `ℐ_Z = ℐ 𝒪_Z`. -/
public theorem idealPowerMultiple_comap_eq_bot_of_pushforward_eq_bot
    (I : X.IdealSheafData) (n : ℕ) (G : Z.Modules) [G.IsQuasicoherent]
    (hG : idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G) = ⊥) :
    idealPowerMultiple (I.comap i) n G = ⊥ := by
  have : IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n ((Scheme.Modules.pushforward i).obj G)).ι) :=
    isIso_cokernel_π_of_eq_bot _ hG
  have : IsIso ((Scheme.Modules.pushforward i).map
      (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι)) := by
    rw [← pushforwardIdealPowerQuotientIso_π i I n G]
    infer_instance
  have : IsIso (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι) :=
    (Stacks.ClosedImmersion.fullyFaithfulPushforward i).isIso_of_isIso_map _
  exact (submodule_ι_eq_zero_iff _).1 <|
    (cancel_mono (cokernel.π (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι)).1
      ((cokernel.condition (C := Z.Modules) (idealPowerMultiple (I.comap i) n G).ι).trans
        (zero_comp (C := Z.Modules)).symm)

/-! ### Termwise direct image detects coherent adic systems -/

/-- **Termwise direct image along a closed immersion detects coherent adic systems.** Let
`(G_n)` be an inverse system of *coherent* `𝒪_Z`-modules whose termwise direct image `(i_* G_n)`
is a coherent adic system along `ℐ`. Then `(G_n)` is a coherent adic system along
`ℐ_Z = ℐ 𝒪_Z`. -/
public theorem isCoherentAdicSystem_comap_of_pushforward (I : X.IdealSheafData)
    {G : ℕᵒᵖ ⥤ Z.Modules} (hcoh : ∀ n : ℕᵒᵖ, (G.obj n).IsCoherent)
    (hpush : IsCoherentAdicSystem I (G ⋙ Scheme.Modules.pushforward i)) :
    IsCoherentAdicSystem (I.comap i) G := by
  let hff := Stacks.ClosedImmersion.fullyFaithfulPushforward i
  have hqc : ∀ n : ℕᵒᵖ, (G.obj n).IsQuasicoherent := fun n =>
    have := hcoh n
    isQuasicoherent_of_isCoherent (G.obj n)
  refine ⟨fun n => hcoh (op n), fun n => ?_, fun n => ?_⟩
  · have := hqc (op n)
    exact idealPowerMultiple_comap_eq_bot_of_pushforward_eq_bot i I (n + 1) (G.obj (op n))
      (hpush.idealPowerMultiple_eq_bot n)
  · have := hqc (op (n + 1))
    set α := pushforwardIdealPowerQuotientIso i I (n + 1) (G.obj (op (n + 1)))
    set q := hpush.quotientIso n
    refine ⟨hff.preimageIso (α.symm ≪≫ q), hff.map_injective ?_⟩
    have hπ := pushforwardIdealPowerQuotientIso_π i I (n + 1) (G.obj (op (n + 1)))
    have hpre : (Scheme.Modules.pushforward i).map
        (hff.preimageIso (α.symm ≪≫ q)).hom = α.inv ≫ q.hom :=
      hff.map_preimage (α.symm ≪≫ q).hom
    refine Eq.trans ((Scheme.Modules.pushforward i).map_comp _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ z ≫ (Scheme.Modules.pushforward i).map
      (hff.preimageIso (α.symm ≪≫ q)).hom) hπ.symm) ?_
    refine Eq.trans (congrArg (fun z ↦ (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1)
        ((Scheme.Modules.pushforward i).obj (G.obj (op (n + 1))))).ι ≫ α.hom) ≫ z) hpre) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1)
        ((Scheme.Modules.pushforward i).obj (G.obj (op (n + 1))))).ι ≫ z)
      (α.hom_inv_id_assoc q.hom)) ?_
    exact hpush.cokernel_π_comp_quotientIso n

/-! ### Essential surjectivity -/

variable [IsLocallyNoetherian X]

/-- **Essential surjectivity of termwise direct image along a closed immersion, the adic-system
analogue of [Stacks, Tag 087T].** Let `i : Z ⟶ X` be a closed immersion into a locally
Noetherian scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. A coherent adic system
`(ℱ_n)` along `ℐ` all of whose terms are killed by the ideal sheaf `ker(i)` cutting out `Z` is
the termwise direct image of a coherent adic system along `ℐ 𝒪_Z`. -/
public theorem essImage_coherentAdicPushforwardClosed_of_annihilated (I : X.IdealSheafData)
    (F : CoherentAdicSystems I) (hF : IsSystemAnnihilatedBy i.ker F.obj) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardClosed i I).essImage F := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  let e : F.obj ≅ (F.obj ⋙ Scheme.Modules.pullback i) ⋙ Scheme.Modules.pushforward i :=
    NatIso.ofComponents
      (fun n ↦ @asIso _ _ _ _
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (F.obj.obj n))
        (isIso_unit_app_of_idealPowerMultiple_ker_eq_bot i (F.obj.obj n) (hF n.unop)))
      (fun {_ _} f ↦
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality (F.obj.map f))
  have hcohN : ∀ n : ℕᵒᵖ, ((F.obj ⋙ Scheme.Modules.pullback i).obj n).IsCoherent := fun n ↦
    have := F.property.isCoherent n.unop
    isCoherent_pullback i (F.obj.obj n)
  exact ⟨⟨F.obj ⋙ Scheme.Modules.pullback i,
      isCoherentAdicSystem_comap_of_pushforward i I hcohN
        (isCoherentAdicSystem_of_iso I e F.property)⟩,
    ⟨ObjectProperty.isoMk (IsCoherentAdicSystem I) e.symm⟩⟩

/-! ### The equivalence -/

/-- The coherent adic systems along `ℐ` killed by the ideal sheaf cutting out `Z`, as a property
of objects of `Coh(X, ℐ)`. -/
public abbrev coherentAdicSystemAnnihilatedByKer (I : X.IdealSheafData) :
    ObjectProperty (CoherentAdicSystems I) :=
  fun F => IsSystemAnnihilatedBy i.ker F.obj

/-- Termwise direct image as a functor
`Coh(Z, ℐ 𝒪_Z) ⥤ { (ℱ_n) ∈ Coh(X, ℐ) : ker(i) ℱ_n = 0 }`. -/
public def coherentAdicPushforwardKer (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    CoherentAdicSystems (I.comap i) ⥤
      (coherentAdicSystemAnnihilatedByKer i I).FullSubcategory :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  ObjectProperty.lift _ (coherentAdicPushforwardClosed i I)
    fun G n => idealPowerMultiple_ker_pushforward_eq_bot i (G.obj.obj (op n))

/-- Forgetting the annihilation identifies `Stacks.Coherent.coherentAdicPushforwardKer` with
termwise direct image. -/
public theorem coherentAdicPushforwardKer_comp_ι (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    coherentAdicPushforwardKer i I ⋙ (coherentAdicSystemAnnihilatedByKer i I).ι =
      coherentAdicPushforwardClosed i I := rfl

/-- `Stacks.Coherent.coherentAdicPushforwardKer` is fully faithful. -/
public def fullyFaithfulCoherentAdicPushforwardKer (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardKer i I).FullyFaithful :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  Functor.FullyFaithful.ofCompFaithful
    (G := (coherentAdicSystemAnnihilatedByKer i I).ι)
    (show (coherentAdicPushforwardKer i I ⋙
        (coherentAdicSystemAnnihilatedByKer i I).ι).FullyFaithful from
      fullyFaithfulCoherentAdicPushforwardClosed i I)

/-- `Stacks.Coherent.coherentAdicPushforwardKer` is full. -/
public instance coherentAdicPushforwardKer_full (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardKer i I).Full :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  (fullyFaithfulCoherentAdicPushforwardKer i I).full

/-- `Stacks.Coherent.coherentAdicPushforwardKer` is faithful. -/
public instance coherentAdicPushforwardKer_faithful (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardKer i I).Faithful :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  (fullyFaithfulCoherentAdicPushforwardKer i I).faithful

/-- `Stacks.Coherent.coherentAdicPushforwardKer` is essentially surjective. -/
public instance coherentAdicPushforwardKer_essSurj (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardKer i I).EssSurj :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  { mem_essImage F := by
      obtain ⟨G, ⟨e⟩⟩ :=
        essImage_coherentAdicPushforwardClosed_of_annihilated i I F.obj F.property
      exact ⟨G, ⟨(coherentAdicSystemAnnihilatedByKer i I).isoMk e⟩⟩ }

/-- `Stacks.Coherent.coherentAdicPushforwardKer` is an equivalence. -/
public instance coherentAdicPushforwardKer_isEquivalence (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    (coherentAdicPushforwardKer i I).IsEquivalence :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  { }

/-- **The adic-system analogue of [Stacks, Tag 087T].** For a closed immersion `i : Z ⟶ X` into a
locally Noetherian scheme and a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X`, termwise direct image
is an equivalence from `Coh(Z, ℐ 𝒪_Z)` onto the full subcategory of `Coh(X, ℐ)` of systems all
of whose terms are killed by the ideal sheaf `ker(i)` cutting out `Z`.

Full faithfulness is `Stacks.Coherent.fullyFaithfulCoherentAdicPushforwardClosed`, and essential
surjectivity is `Stacks.Coherent.essImage_coherentAdicPushforwardClosed_of_annihilated`. The
functor of this equivalence composed with the inclusion of the full subcategory *is*
`Stacks.Coherent.coherentAdicPushforwardClosed`, by
`Stacks.Coherent.coherentAdicPushforwardKer_comp_ι`.

The stacks-087T attribute is not repeated here: that tag is the statement about single coherent
modules, which is `Stacks.ClosedImmersion.pushforwardCohEquivalence`. -/
@[ega "III 5.3.5" "partial"]
public def coherentAdicPushforwardKerEquivalence (I : X.IdealSheafData) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    CoherentAdicSystems (I.comap i) ≌
      (coherentAdicSystemAnnihilatedByKer i I).FullSubcategory :=
  letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  (coherentAdicPushforwardKer i I).asEquivalence

end

/-! ### Closed subschemes cut out by an ideal sheaf -/

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-- **Essential surjectivity onto the `𝒦`-annihilated part of `Coh(X, ℐ)`.** Let `X` be a
locally Noetherian scheme and `ℐ, 𝒦 ⊆ 𝒪_X` quasi-coherent sheaves of ideals. Every coherent adic
system along `ℐ` killed by `𝒦` is the termwise direct image, along the closed immersion
`V(𝒦) ⟶ X`, of a coherent adic system along `ℐ 𝒪_{V(𝒦)}`.

This is the shape the inductive step of [Stacks, Tag 088C] needs in order to transport essential
surjectivity *back up* from `V(𝒦)` to `X`: a system killed by `𝒦` becomes a system on `V(𝒦)`,
which the induction hypothesis on `V(𝒦)` algebraizes, and
`Stacks.Coherent.completionPushforwardNatIso` then turns that algebraization into one on `X`. -/
@[ega "III 5.3.5" "partial"]
public theorem essImage_coherentAdicPushforwardClosed_subscheme
    (F : CoherentAdicSystems I) (hF : IsSystemAnnihilatedBy K F.obj) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    (coherentAdicPushforwardClosed K.subschemeι I).essImage F :=
  essImage_coherentAdicPushforwardClosed_of_annihilated K.subschemeι I F fun n ↦ by
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hF n

end

end Stacks.Coherent

end
