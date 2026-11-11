module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata

/-!
# Normalized dualizing complexes restrict along an open immersion

Let `(S, ω_S^•)` be as in Situation [Stacks, Tag 0AU4], let `j : X ⟶ Y` be an open immersion of
schemes of finite type over `S`, and let `ω_X^•`, `ω_Y^•` be the dualizing complexes normalized
relative to `ω_S^•`. Then there is a canonical isomorphism `ω_X^• ≅ ω_Y^•|_X`
([Stacks, Tag 0AUC]).

The restriction `j^! ω_Y^•` is itself normalized relative to `ω_S^•`: an open `W ⊆ X` separated
over `S` is identified by `j` with the open `j(W) ⊆ Y`, and `α_W` is `α_{j(W)}` transported along
`W ≅ j(W)` by the comparisons of [Stacks, Tag 0ATX]. Uniqueness of normalized complexes
([Stacks, Tag 0AU7]) then gives the unique isomorphism `ω_X^• ≅ j^! ω_Y^•` compatible with the
normalizations, and `j^!` is restriction ([Stacks, Tag 0AU0]).

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.shriekOfIsOpenImmersion`: `j^! ω_Y^•`, normalized relative to
  `ω_S^•`.
* `Stacks.Duality.NormalizedOnOpens.isoDerivedRestrictNagata`: **[Stacks, Tag 0AUC]**, the
  canonical isomorphism `ω_X^• ≅ ω_Y^•|_X` in `D(𝒪_X)`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_shriekOfIsOpenImmersion_nagata`:
  **[Stacks, Tag 0AUC]**, exactly one isomorphism `ω_X^• ≅ j^! ω_Y^•` is compatible with the
  normalizations on every open of `X` separated over `S`.
* `Stacks.Duality.NormalizedOnOpens.isoDerivedRestrictNagata_eq`: the canonical isomorphism is
  that unique isomorphism followed by `j^! = j^*`.

## References

* [Stacks Project, Tag 0AUC](https://stacks.math.columbia.edu/tag/0AUC)
* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v'

namespace Stacks.Duality

namespace IsFiniteTypeOverNoetherian

variable {X Y S : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}

/-- An open immersion into a scheme of finite type over a Noetherian base is shriekable. -/
theorem isShriekable_of_isOpenImmersion (hq : IsFiniteTypeOverNoetherian q) (j : X ⟶ Y)
    [IsOpenImmersion j] : IsShriekable j :=
  let := hq.source_noetherian
  let : NoetherianSpace X := j.isOpenEmbedding.isInducing.noetherianSpace
  { target_noetherian := hq.source_noetherian
    separatedFiniteType :=
      ⟨⟨inferInstance, inferInstance⟩, quasiCompact_of_noetherianSpace_source _⟩ }

/-- The image `j(W)` of an open `W ⊆ X` separated over the base, along an open immersion
`j : X ⟶ Y` over the base, is separated over the base. -/
theorem isShriekable_image_of_isOpenImmersion (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) {j : X ⟶ Y} [IsOpenImmersion j] (hpe : j ≫ q = p)
    (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)) : IsShriekable ((j ''ᵁ W).ι ≫ q) :=
  IsShriekable.of_eq (show (j.isoImage W).symm.hom ≫ W.ι ≫ p = (j ''ᵁ W).ι ≫ q by
      rw [Iso.symm_hom, ← hpe, j.isoImage_inv_ι_assoc])
    ((hq.isShriekable_hom_of_iso hp _ _ (j.isoImage W).symm).comp hW)

end IsFiniteTypeOverNoetherian

namespace NormalizedOnOpens

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] {A : UpperShriek 𝒟}
  {X Y S : Scheme.{u}} {j : X ⟶ Y} [IsOpenImmersion j] {q : Y ⟶ S} {p : X ⟶ S}
  (hpe : j ≫ q = p) (hp : IsFiniteTypeOverNoetherian p) {hq : IsFiniteTypeOverNoetherian q}
  {ωS : 𝒟 S}

/-- The normalization isomorphism of `j^! ω_Y^•` on an open `W ⊆ X` separated over the base: the
one of `ω_Y^•` on `j(W)`, transported along `W ≅ j(W)`. -/
def shriekLocalIsoOfIsOpenImmersion (𝒦 : NormalizedOnOpens A hq ωS) (W : X.Opens)
    (hW : IsShriekable (W.ι ≫ p)) :
    A.restrictTo hp W ((A.shriek j (hq.isShriekable_of_isOpenImmersion j)).obj 𝒦.complex) ≅
      A.localModel hW ωS :=
  ((A.factorIso rfl (hp.isShriekable_ι W) (hq.isShriekable_of_isOpenImmersion j)
      ((hp.isShriekable_ι W).comp (hq.isShriekable_of_isOpenImmersion j))).app
        𝒦.complex).symm ≪≫
    A.restrictCompare (j.isoImage_hom_ι W) (by rw [j.isoImage_hom_ι_assoc, hpe])
      (hp.isShriekable_hom_of_iso hq _ _ (j.isoImage W))
      (hq.isShriekable_ι _) (hp.isShriekable_image_of_isOpenImmersion hq hpe W hW)
      ((hp.isShriekable_ι W).comp (hq.isShriekable_of_isOpenImmersion j)) hW
      (𝒦.localIso _ (hp.isShriekable_image_of_isOpenImmersion hq hpe W hW))

/-- **`j^! ω_Y^•` is normalized relative to `ω_S^•`**: for an open immersion `j : X ⟶ Y` over the
base, the upper shriek along `j` of a dualizing complex normalized relative to `ω_S^•`, with the
normalizations `shriekLocalIsoOfIsOpenImmersion`. -/
def shriekOfIsOpenImmersion (𝒦 : NormalizedOnOpens A hq ωS) : NormalizedOnOpens A hp ωS where
  complex := (A.shriek j (hq.isShriekable_of_isOpenImmersion j)).obj 𝒦.complex
  localIso W hW := 𝒦.shriekLocalIsoOfIsOpenImmersion hpe hp W hW
  compat {W'' W'} h hW' hW'' := by
    have h₂ : j ''ᵁ W'' ≤ j ''ᵁ W' := j.image_mono h
    have hr : X.homOfLE h ≫ (j.isoImage W').hom = (j.isoImage W'').hom ≫ Y.homOfLE h₂ :=
      (j.isoImage_hom_homOfLE W'' W' h).symm
    have hc := 𝒦.compat h₂ (hp.isShriekable_image_of_isOpenImmersion hq hpe W' hW')
      (hp.isShriekable_image_of_isOpenImmersion hq hpe W'' hW'')
    rw [UpperShriek.restrictLocalIso_eq_restrictCompare] at hc ⊢
    simp only [shriekLocalIsoOfIsOpenImmersion]
    rw [UpperShriek.restrictCompare_factorIso_symm_trans, ← hc,
      UpperShriek.restrictCompare_comp _ (rfl : X.homOfLE h ≫ _ = _),
      UpperShriek.restrictCompare_comp _ (rfl : (j.isoImage W'').hom ≫ Y.homOfLE h₂ = _)]
    · congr 1
      exact UpperShriek.restrictCompare_congr _ hr _ _ _ _ _ _ _ _ _ _ _
    all_goals first
      | exact (by rw [Category.assoc, Y.homOfLE_ι, j.isoImage_hom_ι] :
          ((j.isoImage W'').hom ≫ Y.homOfLE h₂) ≫ (j ''ᵁ W').ι = W''.ι ≫ j)
      | exact (by rw [Category.assoc, Y.homOfLE_ι_assoc, j.isoImage_hom_ι_assoc, hpe] :
          ((j.isoImage W'').hom ≫ Y.homOfLE h₂) ≫ (j ''ᵁ W').ι ≫ q = W''.ι ≫ p)
      | exact (by rw [Category.assoc, j.isoImage_hom_ι, Scheme.homOfLE_ι_assoc] :
          (X.homOfLE h ≫ (j.isoImage W').hom) ≫ (j ''ᵁ W').ι = W''.ι ≫ j)
      | exact (by rw [Category.assoc, j.isoImage_hom_ι_assoc, Scheme.homOfLE_ι_assoc, hpe] :
          (X.homOfLE h ≫ (j.isoImage W').hom) ≫ (j ''ᵁ W').ι ≫ q = W''.ι ≫ p)
      | exact (hp.isShriekable_hom_of_iso hq _ _ (j.isoImage W'')).comp
          (hq.isShriekable_homOfLE h₂)
      | exact (hp.isShriekable_homOfLE h).comp (hp.isShriekable_hom_of_iso hq _ _ (j.isoImage W'))

/-- The underlying complex of `𝒦.shriekOfIsOpenImmersion hpe hp` is `j^! 𝒦.complex`. -/
@[simp]
theorem shriekOfIsOpenImmersion_complex (𝒦 : NormalizedOnOpens A hq ωS) :
    (𝒦.shriekOfIsOpenImmersion hpe hp).complex =
      (A.shriek j (hq.isShriekable_of_isOpenImmersion j)).obj 𝒦.complex :=
  rfl

end NormalizedOnOpens

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-- For an open immersion `j : X ⟶ Y`, `j^! K` of the formalism of compactifications is the
derived restriction `K|_X` of `K`, as objects of `D(𝒪_X)` ([Stacks, Tag 0AU0]). -/
def shriekObjIsoDerivedRestrict {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsShriekable j)
    [IsOpenImmersion j] (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    (((ofCompactifications c).shriek j hj).obj K).obj.obj ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj K.obj.obj :=
  (ObjectProperty.ι _).mapIso ((shriekOfIsoOfIsOpenImmersion c j hj).app K) ≪≫
    (OpenImmersion.restrictedDerivedRestrictCompιIso j).app K.obj

end UpperShriek

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {j : X ⟶ Y} [IsOpenImmersion j] {q : Y ⟶ S} {p : X ⟶ S}
  (hpe : j ≫ q = p) {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AUC], canonicity.** In Situation 0AU4, let `j : X ⟶ Y` be an open immersion
of schemes of finite type over `S` and `ω_X^•`, `ω_Y^•` dualizing complexes normalized relative to
`ω_S^•`. Exactly one isomorphism `ω_X^• ≅ j^! ω_Y^•` carries the normalization `α_W` of `ω_X^•`
to that of `j^! ω_Y^•` (`shriekOfIsOpenImmersion`) for every open `W ⊆ X` separated over `S`. -/
@[stacks 0AUC "S Noetherian with dualizing complex ω_S, X → Y an open immersion of schemes of \
  finite type over S; the unique isomorphism ω_X^• ≅ j^! ω_Y^• compatible with the \
  normalizations"]
theorem existsUnique_iso_shriekOfIsOpenImmersion_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    ∃! e : 𝒦X.complex ≅
        (UpperShriek.nagata.shriek j (hq.isShriekable_of_isOpenImmersion j)).obj 𝒦Y.complex,
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫
          (𝒦Y.shriekOfIsOpenImmersion hpe hp).localIso W hW = 𝒦X.localIso W hW :=
  existsUnique_iso_ofCompactifications nagataCompactification hωS 𝒦X
    (𝒦Y.shriekOfIsOpenImmersion hpe hp)

/-- **[Stacks, Tag 0AUC]** In Situation 0AU4, let `j : X ⟶ Y` be an open immersion of schemes of
finite type over `S` and `ω_X^•`, `ω_Y^•` dualizing complexes normalized relative to `ω_S^•`.
The canonical isomorphism `ω_X^• ≅ ω_Y^•|_X` in `D(𝒪_X)`: the unique isomorphism
`ω_X^• ≅ j^! ω_Y^•` compatible with the normalizations
(`existsUnique_iso_shriekOfIsOpenImmersion_nagata`), followed by `j^! = j^*`
([Stacks, Tag 0AU0]). -/
@[stacks 0AUC "the resulting canonical isomorphism ω_X^• ≅ ω_Y^•|_X in D(O_X)"]
def isoDerivedRestrictNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    𝒦X.complex.obj.obj ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj 𝒦Y.complex.obj.obj :=
  (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      (existsUnique_iso_shriekOfIsOpenImmersion_nagata hpe hωS 𝒦X 𝒦Y).exists.choose ≪≫
    UpperShriek.shriekObjIsoDerivedRestrict nagataCompactification j
      (hq.isShriekable_of_isOpenImmersion j) 𝒦Y.complex

/-- **[Stacks, Tag 0AUC], the canonical isomorphism is characterised by the normalizations**:
for any isomorphism `e : ω_X^• ≅ j^! ω_Y^•` compatible with the normalizations on every open of
`X` separated over `S`, `isoDerivedRestrictNagata` is `e` followed by `j^! = j^*`. -/
@[stacks 0AUC "the canonical isomorphism ω_X^• ≅ ω_Y^•|_X is characterized through j^! = j^*"]
theorem isoDerivedRestrictNagata_eq
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (e : 𝒦X.complex ≅
      (UpperShriek.nagata.shriek j (hq.isShriekable_of_isOpenImmersion j)).obj 𝒦Y.complex)
    (he : ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
      (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫
        (𝒦Y.shriekOfIsOpenImmersion hpe hp).localIso W hW = 𝒦X.localIso W hW) :
    isoDerivedRestrictNagata hpe hωS 𝒦X 𝒦Y =
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso e ≪≫
        UpperShriek.shriekObjIsoDerivedRestrict nagataCompactification j
          (hq.isShriekable_of_isOpenImmersion j) 𝒦Y.complex := by
  have h := existsUnique_iso_shriekOfIsOpenImmersion_nagata hpe hωS 𝒦X 𝒦Y
  dsimp only [isoDerivedRestrictNagata]
  rw [h.unique h.exists.choose_spec he]

end NormalizedOnOpens

end Stacks.Duality

end
