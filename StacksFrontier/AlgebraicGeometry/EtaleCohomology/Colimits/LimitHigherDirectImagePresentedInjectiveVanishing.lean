module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLocalizedVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionEtaleCohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# The higher direct images of a colimit of injective systems vanish

Let `(X_i, f_{i'i})` and `(S_i, h_{i'i})` be inverse systems of schemes over a nonempty directed
set with affine transition morphisms, `g_i : X_i ⟶ S_i` a morphism of the first into the second
with every `g_i` quasi-compact and quasi-separated, `X = lim X_i`, `S = lim S_i` and
`g : X ⟶ S` the limit morphism. Let `(F_i)` be a system of abelian sheaves on the `X_i` in the
sense of [Stacks, Tag 0EZL] with every `F_i` injective, and `𝓕 = colim f_i^{-1}F_i`. Then
`R^p g_* 𝓕 = 0` for every `p > 0`.

This is the source's "for any `U` affine and étale over `S` by Theorem 09YQ we have
`H^p(U ×_S X, 𝓕) = colim H^p(U_i ×_{S_i} X_i, 𝓕_i) = 0`" in the proof of [Stacks, Tag 0EYM]:
the higher direct image vanishes as soon as the cohomology of `𝓕` over `U ×_S X` vanishes for the
members `U` of a covering family of every object of `S_étale`
(`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`); the
affine objects form such a family; an affine `U` étale over `S` is the base change of an affine
`U_i` étale over some `S_i` (`Stacks.EtaleCohomology.exists_affine_etale_model_of_isLimit`), so
that `U ×_S X ≅ (U_i ×_{S_i} X_i) ×_{X_i} X`; and the cohomology of `𝓕` over the latter vanishes
by [Stacks, Tag 09YQ] over the localisation,
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.subsingleton_H_localized`.

## Main results

* `Stacks.EtaleCohomology.affineEtalePresieve`,
  `Stacks.EtaleCohomology.generate_affineEtalePresieve_mem` — the objects with affine underlying
  scheme cover every object of the small étale site.
* `Stacks.EtaleCohomology.isZero_rightDerived_sheafSections_mk_of_subsingleton` — derived
  sections over an étale `U ⟶ X` vanish when the étale cohomology of the restriction to `U` does.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.baseChangeModelIso` — `U ×_S X` for a model of
  `U` at a stage.
* `LimitHigherDirectImage.isZero_rightDerived_limitMorphism_of_injective_presentedSystem`
  — **the vanishing.**

## References

* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology

universe v u

namespace Stacks.EtaleCohomology

/-! ### Affine objects cover the small étale site -/

/-- The morphisms into an object of the small étale site whose source has affine underlying
scheme. -/
def affineEtalePresieve {S : Scheme.{u}} (V : S.Etale) : Presieve V :=
  fun W _ => IsAffine W.left

/-- **The affine objects cover every object of the small étale site**: the members of an affine
open cover of the underlying scheme are among them. -/
theorem generate_affineEtalePresieve_mem {S : Scheme.{u}} (V : S.Etale) :
    Sieve.generate (affineEtalePresieve V) ∈ smallEtaleTopology S V := by
  let C := V.left.affineCover
  let W (i : C.I₀) : S.Etale := .mk (C.f i ≫ V.hom)
  let a (i : C.I₀) : W i ⟶ V := MorphismProperty.Over.homMk (C.f i)
  have ha : Sieve.ofArrows _ a ∈ smallEtaleTopology S V :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr <| Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.mpr (C.exists_eq x)
  refine (smallEtaleTopology S).superset_covering ?_ ha
  rintro T b ⟨Z, c, _, ⟨i⟩, hc⟩
  exact ⟨W i, c, a i, inferInstanceAs (IsAffine (C.X i)), hc⟩

/-- The base change of an étale object of a slice, as a morphism. -/
instance etale_overPullback_obj_hom {Y Z : Scheme.{u}} (f : Y ⟶ Z) (A : Over Z) [Etale A.hom] :
    Etale ((Over.pullback f).obj A).hom :=
  MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback A.hom f) inferInstance

/-! ### Derived sections over an object -/

section Sections

variable {X : Scheme.{u}}

/-- Derived sections over isomorphic objects of the small étale site vanish together. -/
theorem isZero_rightDerived_sheafSections_of_iso {W W' : X.Etale} (e : W ≅ W') (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (h : IsZero ((((sheafSections (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (op W')).rightDerived n).obj F)) :
    IsZero ((((sheafSections (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (op W)).rightDerived n).obj F) :=
  h.of_iso ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
    ((sheafSections (smallEtaleTopology X) AddCommGrpCat.{u + 1}).mapIso e.op) n).app F).symm

/-- **Derived sections over an étale `j : U ⟶ X` vanish when the étale cohomology of the
restriction to `U` does**: derived sections over `U` are the étale cohomology of `U` with
coefficients in the restriction (`Stacks.EtaleCohomology.rightDerivedSectionsOverObjectIso`),
and the restriction is the inverse image along `j`
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`). -/
theorem isZero_rightDerived_sheafSections_mk_of_subsingleton {U : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (n : ℕ) (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (h : Subsingleton (Sheaf.H ((etaleAbelianInverseImage.{u, u + 1} j).obj F) n)) :
    IsZero ((((sheafSections (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (op (Etale.mk j))).rightDerived n).obj F) := by
  have h₁ := (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1,
    u, u + 1} (smallEtaleTopology U) _ n).mp h
  have h₂ := h₁.of_iso (((Sheaf.Γ (smallEtaleTopology U) AddCommGrpCat.{u + 1}).rightDerived
    n).mapIso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} j).app F)).symm
  have h₃ := h₂.of_iso ((rightDerivedSectionsOverObjectIso.{u + 1} (Etale.mk j) n).app F)
  exact h₃.of_iso ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
    (sheafSectionsNatIsoEvaluation (smallEtaleTopology X) AddCommGrpCat.{u + 1}) n).app F)

end Sections

namespace LimitHigherDirectImage

variable {I : Type v} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{max u v}} (γ : DX ⟶ DS)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) [IsDirected I (· ≤ ·)]

/-! ### `U ×_S X` for a model of `U` at a stage -/

/-- **`U ×_S X` for a model of `U` at a stage.** If `U ≅ U_i ×_{S_i} S`, then `U ×_S X` is
`(U_i ×_{S_i} X_i) ×_{X_i} X`, as objects of the small étale site of `X`. -/
def baseChangeModelIso (i : Iᵒᵖ) (A : Over (DS.obj i)) [Etale A.hom] {W : cS.pt.Etale}
    (e : Over.mk W.hom ≅ (Over.pullback (cS.π.app i)).obj A) :
    (smallEtaleBaseChange (limitMorphism γ cX cS hcS)).obj W ≅
      Etale.mk (localizedLimitMap DX i.unop ((Over.pullback (γ.app i)).obj A).hom cX) :=
  (Etale.forget cX.pt).preimageIso
    ((Over.pullback (limitMorphism γ cX cS hcS)).mapIso e ≪≫
      ((Over.pullbackComp (limitMorphism γ cX cS hcS) (cS.π.app i)).app A).symm ≪≫
      eqToIso (congrArg (fun f => (Over.pullback f).obj A) (limitMorphism_comp_π γ cX cS hcS i)) ≪≫
      (Over.pullbackComp (cX.π.app i) (γ.app i)).app A)

/-! ### The vanishing -/

variable [Nonempty I]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (γ.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (γ.app i)]

/-- **The higher direct images of a colimit of injective systems vanish.** Let `X = lim X_i` and
`S = lim S_i` with affine transition morphisms over a nonempty directed set, `g_i : X_i ⟶ S_i`
quasi-compact and quasi-separated with limit `g : X ⟶ S`, and `E` a presented system all of whose
sheaves are injective. Then the higher direct images along `g` of the sheaf presenting `E` vanish
in every positive degree. -/
theorem isZero_rightDerived_limitMorphism_of_injective_presentedSystem (hcX : IsLimit cX)
    (E : PresentedSystem (c := cX) IsColimitPresentation)
    (hinj : ∀ i : Iᵒᵖ, Injective (E.sys.obj i)) (q : ℕ) :
    IsZero (((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerived (q + 1)).obj
      E.sheaf) := by
  unfold smallEtalePushforwardAb
  refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (smallEtaleBaseChange (limitMorphism γ cX cS hcS)) (q + 1) E.sheaf fun V =>
      ⟨affineEtalePresieve V, generate_affineEtalePresieve_mem V, fun W _ hW => ?_⟩
  have : IsAffine (Over.mk W.hom).left := hW
  have : Etale (Over.mk W.hom).hom := W.prop
  obtain ⟨i, A, _, _, ⟨e⟩⟩ := exists_affine_etale_model_of_isLimit DS cS hcS (Over.mk W.hom)
  have : CompactSpace ((Over.pullback (γ.app i)).obj A).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst A.hom (γ.app i))
  have : QuasiSeparated (pullback.fst A.hom (γ.app i)) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback A.hom (γ.app i)).flip inferInstance
  have : QuasiSeparatedSpace ((Over.pullback (γ.app i)).obj A).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst A.hom (γ.app i))
  exact isZero_rightDerived_sheafSections_of_iso (baseChangeModelIso γ cX cS hcS i A e) (q + 1)
    E.sheaf (isZero_rightDerived_sheafSections_mk_of_subsingleton _ (q + 1) E.sheaf
      (subsingleton_H_localized DX i.unop ((Over.pullback (γ.app i)).obj A).hom cX hcX E hinj q))

end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
