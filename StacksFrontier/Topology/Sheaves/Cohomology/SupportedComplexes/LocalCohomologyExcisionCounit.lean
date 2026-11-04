module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologyExcisionRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalToGlobalSectionsWithSupport
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardRestrictMate

/-!
# Degreewise excision for sections with support is compatible with the counit of Tag 0G6P

Let `f : X' ⟶ X` be an open immersion of ringed spaces, let `Z ⊆ X` be closed with preimage
`Z' = f^{-1}(Z)`, and write `i : (Z, 𝒪_X|_Z) ⟶ X` and `i' : (Z', 𝒪_{X'}|_{Z'}) ⟶ X'` for the two
inclusions and `f|_{Z'}` for the restriction of `f`.  Three isomorphisms attached to this square
have been constructed separately:

* `Stacks.Cohomology.SupportedComplexes.closedSubsetPushforwardPullbackNatIso`, the underived
  base change `i_* ⋙ f^* ≅ (f|_{Z'})^* ⋙ i'_*`;
* `Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedPullbackNatIso`, degreewise
  excision `H_Z ⋙ (f|_{Z'})^* ≅ f^* ⋙ H_{Z'}` for the functor `H_Z` of [Stacks, Tag 0G6N];
* the counit `i_* H_Z(-) ⟶ id` of the adjunction `i_* ⊣ H_Z` of [Stacks, Tag 0G6P].

This file proves that the three fit together: transporting the counit on `X` along excision and
along base change gives the counit on `X'`.  That is
`closedSubsetPushforwardPullbackNatIso_comp_counit`, the main result, and it is the coherence an
excision statement for the *triangle* of [Stacks, Tag 0G6R] — the one whose third term is the
sections away from `Z` — has to be fed.

## Main results

* `pullbackCompIso_eq_modulePullbackComp`: the two constructions of the pullback-composition
  isomorphism `(a ≫ b)^* ≅ b^* ⋙ a^*` of [Stacks, Tag 0097] part (2) in the development,
  `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso` and
  `RingedSpaceModuleAdjunction.modulePullbackComp`, are the same isomorphism.
* `pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso` and
  `closedSubsetRestrictionPullbackSquareIso_comp_pullbackCompSquare`: the two-square
  `Stacks.Cohomology.pullbackCompSquare` of the restriction square is inverse to
  `closedSubsetRestrictionPullbackSquareIso`.
* `supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι`: **excision for the subsheaf of
  sections supported on `Z` is compatible with its inclusion into the coefficient module.**
* `closedSubsetPushforwardPullbackNatIso_comp_map_eq`: base change followed by `i'_*` of
  degreewise excision is degreewise excision for the *subsheaf* of supported sections, read
  through the two identifications `i_* H_Z ≅ S_Z` of
  `Stacks.SheafOfModules.SupportedSections`
  `.supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`.
* `closedSubsetPushforwardPullbackNatIso_comp_counit` and
  `closedSubsetPushforwardPullbackNatIso_comp_counit_natTrans`: **the main result**, at an object
  and as an equality of natural transformations.

## Implementation notes

**Why the pullback-composition isomorphisms have to be identified.**  The base change of the
square is a mate of `Stacks.Cohomology.pullbackCompSquare` by
`closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv`, and that two-square is assembled from
`RingedSpaceModuleAdjunction.modulePullbackComp`; whereas
`closedSubsetRestrictionPullbackSquareIso`, which is what degreewise excision for `H_Z` is built
from, is assembled from `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso`.  Both are
produced from the pushforward-composition isomorphism by uniqueness of left adjoints, so they
agree, and `pullbackCompIso_eq_modulePullbackComp` says so by comparing their images under
`CategoryTheory.conjugateEquiv`, which is injective.  Without that identification the leading
factor of the mate computation does not cancel.

**The route.**  The main result is proved in two steps.  The first,
`closedSubsetPushforwardPullbackNatIso_comp_map_eq`, is checked after transposing along
`i'^* ⊣ i'_*`: the transpose of the base change is computed by `CategoryTheory.mateEquiv_counit`,
the counit of `i'^* ⊣ i'_*` is slid past degreewise excision by naturality, degreewise excision is
unfolded, and the leading comparison of iterated pullbacks cancels against
`closedSubsetRestrictionPullbackSquareIso`.  The second step feeds that to
`Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq`, which writes the counit of
[Stacks, Tag 0G6P] as the identification `i_* H_Z ≅ S_Z` followed by the inclusion of the
subsheaf, and to `supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι`.

**The compatibility of excision with the inclusion.**
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` is built in three
factors: the comparison for the concrete restriction `immRestrict f`, conjugated by
`Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback`.  The middle factor's
compatibility with the two inclusions is exactly the `choose_spec` of
`exists_supportedSectionsImmRestrictIso`, and the two copies of `immRestrictIsoPullback` are
absorbed by its naturality at the inclusion.  So no statement about sections is needed.

**Diagram chases at a variable category.**  The categories of sheaves of modules here are large
enough that `simp` and `rw` on a goal stated in them exhaust the heartbeat budget.  Each formal
chase is therefore hoisted into a `private theorem` at a variable category with the objects
implicit and the morphisms explicit, and applied with a single `exact`.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Lemma 17.6.3 (Tag 0097)](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

/-! ### The two constructions of the pullback-composition isomorphism -/

section Comp

variable {X Y W : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ W)

/-- `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso` unfolded: it is the comparison of
the two left adjoints of `(a ≫ b)_*`, the second being the composite of the two adjunctions read
through `RingedSpaceModuleAdjunction.modulePushforwardComp`. -/
private theorem pullbackCompIso_eq_leftAdjointUniq :
    RelativeMayerVietoris.pullbackCompIso a b =
      Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (a ≫ b))
        (((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction a)).ofNatIsoRight
            (modulePushforwardComp a b)) := rfl

/-- The conjugate of the inverse of `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso` is
the inverse of the pushforward-composition isomorphism.  This is what
`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom` computes, the inverse
being the direction in which the transported adjunction comes first. -/
private theorem conjugateEquiv_pullbackCompIso_inv :
    conjugateEquiv (modulePullbackPushforwardAdjunction (a ≫ b))
        ((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction a))
        (RelativeMayerVietoris.pullbackCompIso a b).inv =
      (modulePushforwardComp a b).inv := by
  rw [pullbackCompIso_eq_leftAdjointUniq]
  rw [show (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (a ≫ b))
        (((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction a)).ofNatIsoRight
            (modulePushforwardComp a b))).inv =
      (Adjunction.leftAdjointUniq
        (((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction a)).ofNatIsoRight
            (modulePushforwardComp a b))
        (modulePullbackPushforwardAdjunction (a ≫ b))).hom from
      NatTrans.ext (funext fun _ => Adjunction.leftAdjointUniq_inv_app _ _ _)]
  exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

/-- The conjugate of `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso` is the
pushforward-composition isomorphism: conjugation takes a pair of mutually inverse transformations
to a pair of mutually inverse transformations, so this follows from
`conjugateEquiv_pullbackCompIso_inv`. -/
private theorem conjugateEquiv_pullbackCompIso_hom :
    conjugateEquiv ((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction a))
        (modulePullbackPushforwardAdjunction (a ≫ b))
        (RelativeMayerVietoris.pullbackCompIso a b).hom =
      (modulePushforwardComp a b).hom := by
  have h := conjugateEquiv_comm
    ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction a))
    (modulePullbackPushforwardAdjunction (a ≫ b))
    (α := (RelativeMayerVietoris.pullbackCompIso a b).hom)
    (β := (RelativeMayerVietoris.pullbackCompIso a b).inv)
    (RelativeMayerVietoris.pullbackCompIso a b).inv_hom_id
  rw [conjugateEquiv_pullbackCompIso_inv] at h
  exact ((modulePushforwardComp a b).comp_inv_eq.mp h).trans (Category.id_comp _)

/-- **The two constructions of the pullback-composition isomorphism of [Stacks, Tag 0097] part
(2) in the development agree.**  `Stacks.Cohomology.RelativeMayerVietoris.pullbackCompIso` is
`Stacks.RingedSpace.ModuleFunctors.pullbackComp`, built by uniqueness of left adjoints, and
`RingedSpaceModuleAdjunction.modulePullbackComp` is Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp`; both are determined by their conjugate under
`CategoryTheory.conjugateEquiv`, which is the pushforward-composition isomorphism either way. -/
theorem pullbackCompIso_eq_modulePullbackComp :
    RelativeMayerVietoris.pullbackCompIso a b = modulePullbackComp a b :=
  Iso.ext ((conjugateEquiv _ _).injective
    ((conjugateEquiv_pullbackCompIso_hom a b).trans
      (conjugateEquiv_modulePullbackComp_hom a b).symm))

end Comp

/-! ### The two comparisons of iterated pullbacks around the restriction square -/

section Square

/-- The formal chase behind
`pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso`: two composites of three
factors whose matching factors cancel in pairs compose to the identity. -/
private theorem pullbackSquare_chase {C : Type*} [Category* C] {U V T S : C}
    (bi : U ⟶ V) (e' : V ⟶ T) (ah : T ⟶ S) (ai : S ⟶ T) (e : T ⟶ V) (bh : V ⟶ U)
    (ha : ah ≫ ai = 𝟙 T) (he : e' ≫ e = 𝟙 V) (hb : bi ≫ bh = 𝟙 U) :
    (bi ≫ e' ≫ ah) ≫ ai ≫ e ≫ bh = 𝟙 U := by
  rw [Category.assoc, Category.assoc, ← Category.assoc ah, ha, Category.id_comp,
    ← Category.assoc e', he, Category.id_comp, hb]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) (Z : Set X.carrier)

/-- `closedSubsetRestrictionPullbackSquareIso` rewritten in the
`RingedSpaceModuleAdjunction.modulePullbackComp` spelling, by
`pullbackCompIso_eq_modulePullbackComp`. -/
private theorem closedSubsetRestrictionPullbackSquareIso_hom_eq :
    (closedSubsetRestrictionPullbackSquareIso f Z).hom =
      (modulePullbackComp (closedSubsetRestriction f Z) (closedSubsetInclusion X Z)).inv ≫
        eqToHom (congrArg modulePullback
          (closedSubsetRestriction_comp_closedSubsetInclusion f Z)) ≫
        (modulePullbackComp (closedSubsetInclusion X' (closedSubsetPreimage f Z)) f).hom := by
  show (RelativeMayerVietoris.pullbackCompIso (closedSubsetRestriction f Z)
        (closedSubsetInclusion X Z)).inv ≫ _ ≫
      (RelativeMayerVietoris.pullbackCompIso
        (closedSubsetInclusion X' (closedSubsetPreimage f Z)) f).hom = _
  rw [pullbackCompIso_eq_modulePullbackComp, pullbackCompIso_eq_modulePullbackComp]
  rfl

/-- **The comparison of the two iterated pullbacks around the square of the restriction is
inverse to `closedSubsetRestrictionPullbackSquareIso`.**  Both are composites of the two
pullback-composition isomorphisms of [Stacks, Tag 0097] part (2) and the transport along the
commutativity of the square, read in opposite directions; they agree by
`pullbackCompIso_eq_modulePullbackComp`.

No hypothesis on `f` and no closedness of `Z`: this is pseudofunctoriality of pullback. -/
theorem pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso
    (w : closedSubsetRestriction f Z ≫ closedSubsetInclusion X Z =
      closedSubsetInclusion X' (closedSubsetPreimage f Z) ≫ f) :
    (Stacks.Cohomology.pullbackCompSquare (closedSubsetInclusion X Z)
          (closedSubsetRestriction f Z) f
          (closedSubsetInclusion X' (closedSubsetPreimage f Z)) w).natTrans ≫
        (closedSubsetRestrictionPullbackSquareIso f Z).hom =
      𝟙 _ := by
  rw [closedSubsetRestrictionPullbackSquareIso_hom_eq]
  show ((modulePullbackComp (closedSubsetInclusion X' (closedSubsetPreimage f Z)) f).inv ≫
      eqToHom (congrArg modulePullback w.symm) ≫
      (modulePullbackComp (closedSubsetRestriction f Z) (closedSubsetInclusion X Z)).hom) ≫ _ = _
  exact pullbackSquare_chase _ _ _ _ _ _ (Iso.hom_inv_id _)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _)) (Iso.inv_hom_id _)

/-- `pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso` in the other order. -/
theorem closedSubsetRestrictionPullbackSquareIso_comp_pullbackCompSquare
    (w : closedSubsetRestriction f Z ≫ closedSubsetInclusion X Z =
      closedSubsetInclusion X' (closedSubsetPreimage f Z) ≫ f) :
    (closedSubsetRestrictionPullbackSquareIso f Z).hom ≫
        (Stacks.Cohomology.pullbackCompSquare (closedSubsetInclusion X Z)
          (closedSubsetRestriction f Z) f
          (closedSubsetInclusion X' (closedSubsetPreimage f Z)) w).natTrans =
      𝟙 _ := by
  exact ((closedSubsetRestrictionPullbackSquareIso f Z).hom_comp_eq_id.2
    ((closedSubsetRestrictionPullbackSquareIso f Z).comp_hom_eq_id.1
      (pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso f Z w)))

end Square

/-! ### Excision for the supported-sections subsheaf respects its inclusion -/

section Inclusion

/-- The formal chase behind `supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι`: the
three factors of the comparison are absorbed one at a time by the naturality of the two
inclusions and of the comparison of the two left adjoints. -/
private theorem result_one_chase {C : Type*} [Category* C] {A B D E G H : C}
    (εi : A ⟶ B) (ch : B ⟶ D) (sε : D ⟶ E) (ιF : E ⟶ G) (ιR : D ⟶ H) (εf : H ⟶ G)
    (rι : B ⟶ H) (εs : B ⟶ A) (fι : A ⟶ G)
    (h1 : sε ≫ ιF = ιR ≫ εf) (h2 : ch ≫ ιR = rι) (h3 : rι ≫ εf = εs ≫ fι)
    (h4 : εi ≫ εs = 𝟙 A) :
    (εi ≫ ch ≫ sε) ≫ ιF = fι := by
  rw [Category.assoc, Category.assoc, h1, ← Category.assoc ch ιR εf, h2, h3,
    ← Category.assoc εi εs fι, h4, Category.id_comp]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-- `Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso` at a module,
unfolded into its three factors: the comparison for the concrete restriction `immRestrict f`,
conjugated by `Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback`. -/
private theorem supportedSectionsPullbackNatIso_hom_app
    (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsPullbackNatIso f Z).hom.app ℱ =
      (immRestrictIsoPullback f).inv.app ((supportedSectionsFunctor X Z).obj ℱ) ≫
        (exists_supportedSectionsImmRestrictIso f Z ℱ).choose.hom ≫
        (supportedSectionsFunctor X' (⇑f.hom.base ⁻¹' Z)).map
          ((immRestrictIsoPullback f).hom.app ℱ) :=
  rfl

/-- **Excision for the subsheaf of sections supported on `Z` is compatible with its inclusion
into the coefficient module**: the comparison `f^*(S_Z ℱ) ≅ S_{Z'}(f^* ℱ)` of
`Stacks.SheafOfModules.SupportedSections.supportedSectionsPullbackNatIso`, followed by the
inclusion `S_{Z'}(f^*ℱ) ⟶ f^*ℱ`, is `f^*` of the inclusion `S_Z ℱ ⟶ ℱ`.

For the concrete restriction `immRestrict f` this is the `choose_spec` of
`Stacks.SheafOfModules.SupportedSections.exists_supportedSectionsImmRestrictIso`; the two copies
of `Stacks.Cohomology.RelativeMayerVietoris.immRestrictIsoPullback` that turn it into a statement
about the abstract pullback are absorbed by that isomorphism's naturality at the inclusion.  No
closedness assumption on `Z` is used. -/
theorem supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι
    (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsPullbackNatIso f Z).hom.app ℱ ≫
        (Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X'
          (closedSubsetPreimage f Z)).app ((modulePullback f).obj ℱ) =
      (modulePullback f).map
        ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X Z).app ℱ) := by
  rw [supportedSectionsPullbackNatIso_hom_app]
  exact result_one_chase _ _ _ _
    ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X'
      (closedSubsetPreimage f Z)).app ((immRestrict f).obj ℱ))
    ((immRestrictIsoPullback f).hom.app ℱ)
    ((immRestrict f).map
      ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X Z).app ℱ))
    ((immRestrictIsoPullback f).hom.app ((supportedSectionsFunctor X Z).obj ℱ)) _
    ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X'
      (closedSubsetPreimage f Z)).naturality ((immRestrictIsoPullback f).hom.app ℱ))
    (exists_supportedSectionsImmRestrictIso f Z ℱ).choose_spec
    ((immRestrictIsoPullback f).hom.naturality
      ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X Z).app ℱ))
    ((immRestrictIsoPullback f).inv_hom_id_app _)

end Inclusion

/-! ### Base change, degreewise excision and the counit of Tag 0G6P -/

section Counit

/-- `closedSubsetPullbackPushforwardIso` is `CategoryTheory.asIso` of the counit of
`i^* ⊣ i_*`, so its forward direction *is* that counit. -/
private theorem closedSubsetPullbackPushforwardIso_hom (Y : RingedSpace.{u, u})
    (W : Set Y.carrier) (hW : IsClosed W) :
    (closedSubsetPullbackPushforwardIso Y W hW).hom =
      (modulePullbackPushforwardAdjunction (closedSubsetInclusion Y W)).counit :=
  rfl

/-- The formal chase behind `closedSubsetPushforwardPullbackNatIso_comp_map_eq`, run on the
transposes: the leading two factors cancel (`ha`), the next pair is exchanged by naturality
(`hb`), and the comparison of iterated pullbacks cancels against the square isomorphism
(`hc`). -/
private theorem counit_transpose_chase {C : Type*} [Category* C]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : C}
    (m : O₁ ⟶ O₂) (k : O₂ ⟶ O₃) (d₁ : O₃ ⟶ O₂) (d₂ : O₂ ⟶ O₄) (d₃ : O₄ ⟶ O₅)
    (d₄ : O₅ ⟶ O₆) (d₅ : O₆ ⟶ O₇) (cn : O₇ ⟶ O₈) (bt : O₂ ⟶ O₁) (q : O₁ ⟶ O₅)
    (ha : k ≫ d₁ = 𝟙 O₂) (hb : d₂ ≫ d₃ = bt ≫ q) (hc : m ≫ bt = 𝟙 O₁) :
    (m ≫ k) ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ d₅ ≫ cn = (q ≫ d₄ ≫ d₅) ≫ cn := by
  rw [Category.assoc m k, ← Category.assoc k d₁, ha, Category.id_comp,
    ← Category.assoc d₂ d₃, hb, Category.assoc bt q, ← Category.assoc m bt, hc,
    Category.id_comp, ← Category.assoc d₄ d₅, ← Category.assoc q]

/-- The formal chase behind `closedSubsetPushforwardPullbackNatIso_comp_counit`: the two
descriptions of the counit of [Stacks, Tag 0G6P] are glued by the invertibility of the
identification `i'_* H_{Z'} ≅ S_{Z'}` (`g₃`) and by excision for the subsheaf (`g₄`). -/
private theorem counit_chase {C : Type*} [Category* C] {P₁ P₂ P₃ P₄ P₅ P₆ : C}
    (s : P₁ ⟶ P₂) (pd : P₂ ⟶ P₃) (c' : P₃ ⟶ P₄) (rh : P₃ ⟶ P₆) (io : P₆ ⟶ P₄)
    (fr : P₁ ⟶ P₅) (a : P₅ ⟶ P₆) (ri : P₆ ⟶ P₃) (fi : P₅ ⟶ P₄) (fc : P₁ ⟶ P₄)
    (g₁ : s ≫ pd = fr ≫ a ≫ ri) (g₂ : c' = rh ≫ io) (g₃ : ri ≫ rh = 𝟙 P₆)
    (g₄ : a ≫ io = fi) (g₅ : fr ≫ fi = fc) :
    s ≫ pd ≫ c' = fc := by
  rw [g₂, ← Category.assoc s pd, g₁, Category.assoc, Category.assoc,
    ← Category.assoc ri rh io, g₃, Category.id_comp, g₄, g₅]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier) (hZ : IsClosed Z) (hZ' : IsClosed (closedSubsetPreimage f Z))

/-- `supportedSectionsOnClosedPullbackNatIso` at a module, unfolded into the six factors of its
definition: the counit `i^* i_* ≅ 𝟭` undone, `i^*` of the identification `i_* H_Z ≅ S_Z`,
pullback read along the square, excision for the subsheaf, the identification on `X'` undone, and
the counit `i'^* i'_* ≅ 𝟭`. -/
private theorem supportedSectionsOnClosedPullbackNatIso_hom_app
    (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ =
      (modulePullback (closedSubsetRestriction f Z)).map
          (𝟙 _ ≫ (closedSubsetPullbackPushforwardIso X Z hZ).inv.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (modulePullback (closedSubsetRestriction f Z)).map
            ((modulePullback (closedSubsetInclusion X Z)).map
              ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ)) ≫
          (closedSubsetRestrictionPullbackSquareIso f Z).hom.app
              ((supportedSectionsFunctor X Z).obj ℱ) ≫
            (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
                ((supportedSectionsPullbackNatIso f Z).hom.app ℱ) ≫
              (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
                  ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
                    (closedSubsetPreimage f Z) hZ').inv.app ((modulePullback f).obj ℱ)) ≫
                ((closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.app
                    ((supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ').obj
                      ((modulePullback f).obj ℱ)) ≫
                  𝟙 _) :=
  rfl

/-- **Base change followed by `i'_*` of degreewise excision for `H_Z` is excision for the
subsheaf of supported sections**, read through the two identifications `i_* H_Z ≅ S_Z` of
`Stacks.SheafOfModules.SupportedSections`
`.supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` on `X` and on `X'`.

Both sides are maps `f^*(i_* H_Z ℱ) ⟶ i'_*(H_{Z'}(f^*ℱ))`, and they are compared after
transposing along `i'^* ⊣ i'_*`: the transpose of the base change is
`CategoryTheory.mateEquiv_counit` applied to
`closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv`, and once degreewise excision is
unfolded the leading comparison of iterated pullbacks cancels by
`pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso`. -/
theorem closedSubsetPushforwardPullbackNatIso_comp_map_eq
    (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (closedSubsetPushforwardPullbackNatIso f Z).hom.app
          ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ) ≫
        (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ) =
      (modulePullback f).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ) ≫
        (supportedSectionsPullbackNatIso f Z).hom.app ℱ ≫
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
            (closedSubsetPreimage f Z) hZ').inv.app ((modulePullback f).obj ℱ) := by
  have hnat : (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
            ((supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ)) ≫
        (closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.app
          ((modulePullback f ⋙
            supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ').obj ℱ) =
      (closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.app
          ((modulePullback (closedSubsetRestriction f Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ :=
    (closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.naturality _
  have hmate : (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((closedSubsetPushforwardPullbackNatIso f Z).hom.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.app
          ((modulePullback (closedSubsetRestriction f Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) =
      (Stacks.Cohomology.pullbackCompSquare (closedSubsetInclusion X Z)
            (closedSubsetRestriction f Z) f
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))
            (isPullback_closedSubsetRestriction f Z).w).natTrans.app
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (modulePullback (closedSubsetRestriction f Z)).map
          ((closedSubsetPullbackPushforwardIso X Z hZ).hom.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) := by
    rw [closedSubsetPushforwardPullbackNatIso_hom_eq_mateEquiv,
      closedSubsetPullbackPushforwardIso_hom, closedSubsetPullbackPushforwardIso_hom]
    exact mateEquiv_counit _ _ _ _
  have hmate' : (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((closedSubsetPushforwardPullbackNatIso f Z).hom.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        ((closedSubsetPullbackPushforwardIso X' (closedSubsetPreimage f Z) hZ').hom.app
            ((modulePullback (closedSubsetRestriction f Z)).obj
              ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
          (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ) =
      ((Stacks.Cohomology.pullbackCompSquare (closedSubsetInclusion X Z)
              (closedSubsetRestriction f Z) f
              (closedSubsetInclusion X' (closedSubsetPreimage f Z))
              (isPullback_closedSubsetRestriction f Z).w).natTrans.app
            ((modulePushforward (closedSubsetInclusion X Z)).obj
              ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
          (modulePullback (closedSubsetRestriction f Z)).map
            ((closedSubsetPullbackPushforwardIso X Z hZ).hom.app
              ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ))) ≫
        (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ := by
    rw [← Category.assoc, hmate]
  have ha : (modulePullback (closedSubsetRestriction f Z)).map
          ((closedSubsetPullbackPushforwardIso X Z hZ).hom.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (modulePullback (closedSubsetRestriction f Z)).map
          ((closedSubsetPullbackPushforwardIso X Z hZ).inv.app
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hb : (modulePullback (closedSubsetRestriction f Z)).map
          ((modulePullback (closedSubsetInclusion X Z)).map
            ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ)) ≫
        (closedSubsetRestrictionPullbackSquareIso f Z).hom.app
          ((supportedSectionsFunctor X Z).obj ℱ) =
      (closedSubsetRestrictionPullbackSquareIso f Z).hom.app
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((modulePullback f).map
            ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ)) :=
    (closedSubsetRestrictionPullbackSquareIso f Z).hom.naturality _
  have hc : (Stacks.Cohomology.pullbackCompSquare (closedSubsetInclusion X Z)
            (closedSubsetRestriction f Z) f
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))
            (isPullback_closedSubsetRestriction f Z).w).natTrans.app
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) ≫
        (closedSubsetRestrictionPullbackSquareIso f Z).hom.app
          ((modulePushforward (closedSubsetInclusion X Z)).obj
            ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ)) =
      𝟙 _ :=
    NatTrans.congr_app (pullbackCompSquare_comp_closedSubsetRestrictionPullbackSquareIso f Z
      (isPullback_closedSubsetRestriction f Z).w) _
  have hs1 := CategoryTheory.Functor.map_comp
    (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
    ((supportedSectionsPullbackNatIso f Z).hom.app ℱ)
    ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
      (closedSubsetPreimage f Z) hZ').inv.app ((modulePullback f).obj ℱ))
  have hsplit := (CategoryTheory.Functor.map_comp
      (modulePullback (closedSubsetInclusion X' (closedSubsetPreimage f Z)))
      ((modulePullback f).map
        ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ))
      ((supportedSectionsPullbackNatIso f Z).hom.app ℱ ≫
        (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
          (closedSubsetPreimage f Z) hZ').inv.app ((modulePullback f).obj ℱ))).trans
    (congrArg (fun t => (modulePullback (closedSubsetInclusion X'
        (closedSubsetPreimage f Z))).map ((modulePullback f).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ)) ≫ t)
      hs1)
  refine (((modulePullbackPushforwardAdjunction
    (closedSubsetInclusion X' (closedSubsetPreimage f Z))).homEquiv _ _).symm).injective ?_
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    ← closedSubsetPullbackPushforwardIso_hom X' (closedSubsetPreimage f Z) hZ']
  refine Eq.trans ?_ (congrArg (fun t => t ≫ _) hsplit.symm)
  rw [Functor.map_comp, Category.assoc, hnat, hmate',
    supportedSectionsOnClosedPullbackNatIso_hom_app, Category.id_comp, Category.comp_id]
  exact counit_transpose_chase _ _ _ _ _ _ _ _ _ _ ha hb hc

/-- **Degreewise excision for sections with support is compatible with the counit of
[Stacks, Tag 0G6P]**, at an `𝒪_X`-module `ℱ`.  Transporting the counit `i_* H_Z(ℱ) ⟶ ℱ` along
`f^*` is the same as reading the counit `i'_* H_{Z'}(f^*ℱ) ⟶ f^*ℱ` through the underived base
change `closedSubsetPushforwardPullbackNatIso` of the square of the restriction and `i'_*` of
degreewise excision `supportedSectionsOnClosedPullbackNatIso`.

By `Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq` either counit is the identification
`i_* H_Z ≅ S_Z` followed by the inclusion of the subsheaf of supported sections, so this reduces
to `closedSubsetPushforwardPullbackNatIso_comp_map_eq` and
`supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι`. -/
theorem closedSubsetPushforwardPullbackNatIso_comp_counit
    (ℱ : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (closedSubsetPushforwardPullbackNatIso f Z).hom.app
          ((supportedSectionsOnClosedFunctor X Z hZ).obj ℱ) ≫
        (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))).map
          ((supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app ℱ) ≫
        (modulePushforward_supportedSectionsOnClosed_adjunction X'
            (closedSubsetPreimage f Z) hZ').counit.app ((modulePullback f).obj ℱ) =
      (modulePullback f).map
        ((modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit.app ℱ) :=
  counit_chase _ _ _ _ _ _ _ _ _ _
    (closedSubsetPushforwardPullbackNatIso_comp_map_eq f Z hZ hZ' ℱ)
    (Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq X' (closedSubsetPreimage f Z) hZ'
      ((modulePullback f).obj ℱ))
    ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X'
      (closedSubsetPreimage f Z) hZ').inv_hom_id_app ((modulePullback f).obj ℱ))
    (supportedSectionsPullbackNatIso_hom_comp_supportedSectionsι f Z ℱ)
    ((CategoryTheory.Functor.map_comp (modulePullback f)
      ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app ℱ)
      ((Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X Z).app ℱ)).symm.trans
      (congrArg (fun t => (modulePullback f).map t)
        (Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq X Z hZ ℱ).symm))

/-- `closedSubsetPushforwardPullbackNatIso_comp_counit` as an equality of natural
transformations `H_Z ⋙ i_* ⋙ f^* ⟶ f^*`. -/
theorem closedSubsetPushforwardPullbackNatIso_comp_counit_natTrans :
    Functor.whiskerLeft (supportedSectionsOnClosedFunctor X Z hZ)
          (closedSubsetPushforwardPullbackNatIso f Z).hom ≫
        Functor.whiskerRight (supportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom
            (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z))) ≫
          Functor.whiskerLeft (modulePullback f)
              (modulePushforward_supportedSectionsOnClosed_adjunction X'
                (closedSubsetPreimage f Z) hZ').counit ≫
            (modulePullback f).rightUnitor.hom =
      Functor.whiskerRight
          (modulePushforward_supportedSectionsOnClosed_adjunction X Z hZ).counit
          (modulePullback f) ≫
        (modulePullback f).leftUnitor.hom := by
  refine NatTrans.ext (funext fun ℱ => ?_)
  show _ ≫ _ ≫ _ ≫ 𝟙 _ = _ ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id]
  exact closedSubsetPushforwardPullbackNatIso_comp_counit f Z hZ hZ' ℱ

end Counit

end Stacks.Cohomology.SupportedComplexes

end
