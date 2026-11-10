module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppf
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCofilteredLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsRestrictionFullness

/-!
# Extending limit preserving sheaves from locally Noetherian schemes on a big fppf site

Let `S` be a locally Noetherian scheme contained in a big fppf site `B`. A functor `F` on the
locally Noetherian site `(Noetherian/S)_étale` of `S` (`AlgebraicGeometry.LocallyNoetherianOver`)
which satisfies the sheaf condition for its étale covering families and is limit preserving in the
sense of Stacks 049J extends to a limit preserving functor on the big fppf site of `S` whose
restriction to the locally Noetherian objects is `F`. This is the existence half of **Stacks 0GE3**
for the big fppf site; its full faithfulness half is
`AlgebraicGeometry.ExtendingFunctors.existsUnique_hom_whiskerLeft_eq_bigFppfOver`.

The extension is the one of Stacks 0EUW
(`AlgebraicGeometry.ExtendingFunctors.extension`), taken for the full subcategory of `Sch/S` on the
locally Noetherian objects contained in `B`, which satisfies conditions (1) and (2) of Stacks 0EUW,
and restricted to the big fppf site of `S`.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.extensionToBigFppfOver`: the extension.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.exists_isEtaleCovering_generate_eq`: every family of the
  locally Noetherian site whose underlying family of schemes is an étale covering generates the
  same sieve as a chosen étale covering family of the site.
* `AlgebraicGeometry.ExtendingFunctors.isCoveringSheafOnSubcategory_etale_of_isSheafFor`: the
  sheaf condition of `F` for the chosen étale coverings gives the sheaf condition for all étale
  coverings by locally Noetherian objects of `Sch/S` contained in `B`.
* `AlgebraicGeometry.ExtendingFunctors.limitPreserving_extensionToBigFppfOver`,
  `AlgebraicGeometry.ExtendingFunctors.nonempty_restriction_extensionToBigFppfOver_iso` and
  `AlgebraicGeometry.ExtendingFunctors.isCoveringSheafOnSubcategory_extensionToBigFppfOver`: the
  extension is limit preserving, restricts to `F`, and is a sheaf for the Zariski coverings.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Presieve

/-- **The sheaf condition for a family transported along a fully faithful essentially surjective
functor.** If `G` satisfies the sheaf condition for the image under `T` of a family of morphisms,
then `T.op ⋙ G` satisfies it for the family itself. -/
theorem isSheafFor_ofArrows_op_comp_of_fullyFaithful {C D : Type*} [Category C] [Category D]
    {T : C ⥤ D} (hT : T.FullyFaithful) [T.EssSurj] {G : Dᵒᵖ ⥤ Type*} {X : C} {ι : Type*}
    {Y : ι → C} (f : ∀ i, Y i ⟶ X)
    (h : (ofArrows (fun i => T.obj (Y i)) (fun i => T.map (f i))).IsSheafFor G) :
    (ofArrows Y f).IsSheafFor (T.op ⋙ G) := by
  rw [isSheafFor_arrows_iff] at h ⊢
  intro x hx
  refine h x fun i j W' a' b' hab => ?_
  let φ : T.obj (T.objPreimage W') ≅ W' := T.objObjPreimageIso W'
  have key : hT.preimage (φ.hom ≫ a') ≫ f i = hT.preimage (φ.hom ≫ b') ≫ f j :=
    hT.map_injective (by simp [hab])
  have h₁ := hx i j _ _ _ key
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    Functor.FullyFaithful.map_preimage, op_comp, Functor.map_comp, types_comp_apply] at h₁
  have h₂ := congrArg (G.map φ.inv.op) h₁
  simpa only [← types_comp_apply (G.map _) (G.map _), ← G.map_comp, ← op_comp,
    Iso.inv_hom_id_assoc] using h₂

end CategoryTheory.Presieve

namespace AlgebraicGeometry

namespace LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor from the locally Noetherian site over `S` to the underlying category of the
big fppf site, forgetting the structure morphism. -/
abbrev toSchemes : LocallyNoetherianOver B S hS ⥤ B.Schemes :=
  toBigFppfOver B S hS ⋙ BigFppfOver.forget B S hS

/-- A pre-`0`-hypercover whose members and arrows agree, after the identifications `h`, with a
reindexing of another one is that reindexing. -/
lemma _root_.CategoryTheory.PreZeroHypercover.eq_restrictIndex {C : Type*} [Category C] {T : C}
    (E : PreZeroHypercover.{w} T) (F : PreZeroHypercover.{v} T) (β : F.I₀ → E.I₀)
    (h : ∀ j, F.X j = E.X (β j)) (hf : ∀ j, F.f j = eqToHom (h j) ≫ E.f (β j)) :
    F = E.restrictIndex β := by
  obtain ⟨I, X, f⟩ := F
  change I → E.I₀ at β
  change ∀ j, X j = E.X (β j) at h
  change ∀ j, f j = eqToHom (h j) ≫ E.f (β j) at hf
  have hX : X = fun j => E.X (β j) := funext h
  subst hX
  simp only [eqToHom_refl, Category.id_comp] at hf
  have hf' : f = fun j => E.f (β j) := funext hf
  subst hf'
  rfl

/-- A morphism of the locally Noetherian site out of an object whose underlying scheme is that of
another object over the same target, and whose underlying morphism is the identification followed
by the other arrow, factors through that other arrow. -/
lemma exists_comp_eq_of_toSchemes {X Y Y' : LocallyNoetherianOver B S hS} (g : Y ⟶ X)
    (g' : Y' ⟶ X) (hY : (toSchemes B S hS).obj Y = (toSchemes B S hS).obj Y')
    (hg : (toSchemes B S hS).map g = eqToHom hY ≫ (toSchemes B S hS).map g') :
    ∃ k : Y ⟶ Y', k ≫ g' = g := by
  have hw : eqToHom hY ≫ Y'.obj.hom = Y.obj.hom := by
    rw [← Over.w g'.hom, ← Category.assoc]
    change (eqToHom hY ≫ (toSchemes B S hS).map g') ≫ X.obj.hom = Y.obj.hom
    rw [← hg]
    exact Over.w g.hom
  refine ⟨ObjectProperty.homMk (Over.homMk (eqToHom hY) hw), ?_⟩
  apply (toSchemes B S hS).map_injective
  rw [Functor.map_comp, hg]
  rfl

/-- **Every étale covering family of the locally Noetherian site has the same sieve as a chosen
one.** A family of morphisms of locally Noetherian objects over `S` whose underlying family of
schemes is an étale covering generates the same sieve as a family which is an étale covering
family of the site in the sense of `AlgebraicGeometry.LocallyNoetherianOver.IsEtaleCovering`. -/
theorem exists_isEtaleCovering_generate_eq {X : LocallyNoetherianOver B S hS}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (toSchemes B S hS ⋙ B.inclusion)).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj ((toSchemes B S hS).obj X))) :
    ∃ E' : PreZeroHypercover.{u + 1} X, IsEtaleCovering B S hS ⟨X, E'⟩ ∧
      Sieve.generate E'.presieve₀ = Sieve.generate E.presieve₀ := by
  have hEs := (Scheme.presieve₀_mem_precoverage_iff _).1 hE
  have hfppf : IsFppfCovering (κ := B.cutoff) ⟨_, E.map (toSchemes B S hS)⟩ := by
    change Presieve.map B.inclusion (E.map (toSchemes B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage.coverings _
    rw [← PreZeroHypercover.presieve₀_map]
    exact (Scheme.presieve₀_mem_precoverage_iff _).2 ⟨hEs.1, fun i =>
      have : Etale (((E.map (toSchemes B S hS)).map B.inclusion).f i) := hEs.2 i
      ⟨inferInstance, inferInstance⟩⟩
  obtain ⟨E₀, hE₀, hcomb⟩ := B.fppf_has_representative ⟨_, E.map (toSchemes B S hS)⟩ hfppf
  obtain ⟨W, F⟩ := E₀
  obtain ⟨hobj, hce⟩ := hcomb
  cases hobj
  dsimp only at hce
  have hpre : F.presieve₀ = (E.map (toSchemes B S hS)).presieve₀ :=
    (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hce).symm
  obtain ⟨⟨α, hα, hαf⟩, ⟨β, hβ, hβf⟩⟩ := hce
  have hFeq : F = (E.restrictIndex β).map (toSchemes B S hS) :=
    PreZeroHypercover.eq_restrictIndex (E.map (toSchemes B S hS)) F β hβ hβf
  refine ⟨E.restrictIndex β, ⟨?_, ?_⟩, ?_⟩
  · rw [← hFeq]
    exact hE₀
  · change (((E.restrictIndex β).map (toSchemes B S hS)).map B.inclusion).presieve₀ ∈ _
    rw [← hFeq, PreZeroHypercover.presieve₀_map, hpre, ← PreZeroHypercover.presieve₀_map]
    exact hE
  · apply le_antisymm
    · exact Sieve.generate_mono (PreZeroHypercover.presieve₀_restrictIndex_le E β)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      have hY : (toSchemes B S hS).obj (E.X i) =
          (toSchemes B S hS).obj (E.X (β (α i))) := (hα i).trans (hβ (α i))
      have hg : (toSchemes B S hS).map (E.f i) =
          eqToHom hY ≫ (toSchemes B S hS).map (E.f (β (α i))) := by
        change (E.map (toSchemes B S hS)).f i = _
        rw [hαf i, hβf (α i), ← Category.assoc, eqToHom_trans]
        rfl
      obtain ⟨k, hk⟩ := exists_comp_eq_of_toSchemes B S hS (E.f i) (E.f (β (α i))) hY hg
      exact ⟨_, k, E.f (β (α i)), Presieve.ofArrows.mk (α i), hk⟩

/-- **An étale sheaf on the locally Noetherian site is a sheaf for the étale coverings of the
locally Noetherian objects of `Sch/S` contained in `B`.** A functor on the locally Noetherian site
satisfying the sheaf condition for its étale covering families satisfies the sheaf condition of
`AlgebraicGeometry.ExtendingFunctors.IsCoveringSheafOnSubcategory` for the étale topology, once
transported along `AlgebraicGeometry.ExtendingFunctors.toLocallyNoetherianOver`. -/
theorem _root_.AlgebraicGeometry.ExtendingFunctors.isCoveringSheafOnSubcategory_etale_of_isSheafFor
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : ∀ E : Covering (LocallyNoetherianOver B S hS), IsEtaleCovering B S hS E →
      E.2.presieve₀.IsSheafFor F) :
    ExtendingFunctors.IsCoveringSheafOnSubcategory.{w, u, v} .etale
      (ExtendingFunctors.IsContainedLocallyNoetherianOver B (S := S))
      ((ExtendingFunctors.toLocallyNoetherianOver B hS).op ⋙ F) := by
  intro ι X Y f hcov
  let T := ExtendingFunctors.toLocallyNoetherianOver B hS
  have hT : T.FullyFaithful :=
    (ExtendingFunctors.locallyNoetherianOverEquivalence B hS).symm.fullyFaithfulFunctor
  have : T.EssSurj := (ExtendingFunctors.locallyNoetherianOverEquivalence B hS).symm.essSurj_functor
  apply Presieve.isSheafFor_ofArrows_op_comp_of_fullyFaithful hT
  obtain ⟨E, hE⟩ := (Presieve.ofArrows (fun i => T.obj (Y i))
    (fun i => T.map (f i))).exists_eq_preZeroHypercover
  rw [ExtendingFunctors.ofArrows_mem_coveringPrecoverage_iff] at hcov
  have hE' : (E.map (toSchemes B S hS ⋙ B.inclusion)).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj ((toSchemes B S hS).obj (T.obj X))) := by
    rw [PreZeroHypercover.presieve₀_map, ← hE, Presieve.map_ofArrows]
    exact (Scheme.ofArrows_mem_precoverage_iff
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).2 ⟨hcov.1, hcov.2⟩
  obtain ⟨E', hE'', hgen⟩ := exists_isEtaleCovering_generate_eq B S hS E hE'
  rw [hE, Presieve.isSheafFor_iff_generate, ← hgen, ← Presieve.isSheafFor_iff_generate]
  exact hF ⟨_, E'⟩ hE''

end LocallyNoetherianOver

namespace ExtendingFunctors

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **A limit preserving functor on the locally Noetherian site of `S` satisfies condition (b) of
Stacks 0EUW**: transported to the locally Noetherian objects of `Sch/S` contained in `B`, it
carries a directed inverse limit of affine objects whose limit lies in that subcategory to a
filtered colimit. -/
theorem preservesAffineLimitsOnSubcategory_of_limitPreserving_locallyNoetherian
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : LimitPreserving.{u, w, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS) F) :
    PreservesAffineLimitsOnSubcategory (IsContainedLocallyNoetherianOver B (S := S))
      ((toLocallyNoetherianOver B hS).op ⋙ F) := by
  intro Λ _ _ _ D haff c hc
  have : ∀ i : Λᵒᵖ, IsAffine (((D ⋙ (IsContainedLocallyNoetherianOver B).ι) ⋙
      Over.forget S).obj i) := haff
  have hlim : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone
      ((toLocallyNoetherianOver B hS).mapCone c)) :=
    isLimitOfPreserves (Over.forget S) hc
  have hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj
      ((toLocallyNoetherianOver B hS).mapCone c).pt) :=
    Scheme.isAffine_of_isLimit _ (isLimitOfPreserves (Over.forget S) hc)
  exact hF Λᵒᵖ (D ⋙ toLocallyNoetherianOver B hS) ((toLocallyNoetherianOver B hS).mapCone c) hlim
    haff hpt

/-- The functor from the big fppf site of `S` to `Sch/S`. -/
abbrev bigFppfOverToOver : BigFppfOver B S hS ⥤ Over S :=
  fromBigFppfOver B hS ⋙ (IsContainedOver B (S := S)).ι

/-- **The restriction of a limit preserving functor on `Sch/S` to the big fppf site of `S` is
limit preserving in the sense of Stacks 049J.** -/
theorem limitPreserving_restriction_of_preservesAffineLimits
    {G : (Over S)ᵒᵖ ⥤ Type w} (hG : PreservesAffineLimits G) :
    LimitPreserving.{u, w, u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      ((bigFppfOverToOver B hS).op ⋙ G) := by
  intro I _ _ D c hc haff _
  have hG' := Scheme.isLimitPreserving_of_preservesAffineLimits hG I
    (D ⋙ bigFppfOverToOver B hS) haff
  have : IsConnected I := IsCofiltered.isConnected I
  have hK : IsLimit ((bigFppfOverToOver B hS).mapCone c) :=
    isLimitOfReflects (Over.forget S) hc
  exact ⟨isColimitOfPreserves G hK.op⟩

/-- An étale sheaf on the locally Noetherian site gives a Zariski sheaf on the subcategory. -/
private theorem isZariskiSheafOnSubcategory_of_isSheafFor
    {F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : ∀ E : Covering (LocallyNoetherianOver B S hS),
      LocallyNoetherianOver.IsEtaleCovering B S hS E → E.2.presieve₀.IsSheafFor F) :
    IsZariskiSheafOnSubcategory (IsContainedLocallyNoetherianOver B (S := S))
      ((toLocallyNoetherianOver B hS).op ⋙ F) :=
  isZariskiSheafOnSubcategory_of_isCoveringSheafOnSubcategory .etale
    (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (isCoveringSheafOnSubcategory_etale_of_isSheafFor B S hS hF)

variable [IsLocallyNoetherian S] (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1)))

/-- **The extension to the big fppf site of a functor on the locally Noetherian site.** The functor
on the locally Noetherian objects of `Sch/S` contained in `B` corresponding to `F` is extended to
`Sch/S` by Stacks 0EUW, and the extension is restricted to the big fppf site of `S`. -/
noncomputable def extensionToBigFppfOver : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w (u + 1)) :=
  (bigFppfOverToOver B hS).op ⋙
    extension (IsContainedLocallyNoetherianOver B (S := S)) ((toLocallyNoetherianOver B hS).op ⋙ F)

variable {B hS F}

variable (hFs : ∀ E : Covering (LocallyNoetherianOver B S hS),
      LocallyNoetherianOver.IsEtaleCovering B S hS E → E.2.presieve₀.IsSheafFor F)
    (hFl : LimitPreserving.{u, max w (u + 1), u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) F)

include hFs hFl in
/-- The extension on `Sch/S` underlying
`AlgebraicGeometry.ExtendingFunctors.extensionToBigFppfOver` is a limit preserving sheaf for the
étale topology. -/
theorem isLimitPreservingSheaf_extension_locallyNoetherian :
    IsLimitPreservingSheaf .etale
      (extension (IsContainedLocallyNoetherianOver B (S := S))
        ((toLocallyNoetherianOver B hS).op ⋙ F)) :=
  isLimitPreservingSheaf_extension .etale (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS) _
    ⟨isCoveringSheafOnSubcategory_etale_of_isSheafFor B S hS hFs,
      preservesAffineLimitsOnSubcategory_of_limitPreserving_locallyNoetherian B hS hFl⟩

include hFs hFl in
/-- **The extension of a limit preserving functor on the locally Noetherian site is limit
preserving** in the sense of Stacks 049J. -/
theorem limitPreserving_extensionToBigFppfOver :
    LimitPreserving.{u, max w (u + 1), u, u, u + 1, u} (BigFppfOver.toScheme B S hS)
      (extensionToBigFppfOver B hS F) :=
  limitPreserving_restriction_of_preservesAffineLimits B hS
    (isLimitPreservingSheaf_extension_locallyNoetherian hFs hFl).2

include hFs hFl in
/-- **The extension restricts to the given functor on the locally Noetherian site.** -/
theorem nonempty_restriction_extensionToBigFppfOver_iso :
    Nonempty ((LocallyNoetherianOver.toBigFppfOver B S hS).op ⋙
      extensionToBigFppfOver B hS F ≅ F) := by
  obtain ⟨e⟩ := nonempty_restrictionIso _ (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS)
    (isZariskiSheafOnSubcategory_of_isSheafFor B hS hFs)
    (preservesAffineLimitsOnSubcategory_of_limitPreserving_locallyNoetherian B hS hFl)
  exact ⟨Functor.isoWhiskerLeft (fromLocallyNoetherianOver B hS).op e⟩

omit [IsLocallyNoetherian S] in
/-- **The objects of `Sch/S` contained in `B` contain the fibre products along open
immersions.** -/
theorem hasCoveringPullbacks_zariski_isContainedOver :
    HasCoveringPullbacks .zariski (IsContainedOver B (S := S)) := by
  intro X Y Z p q hY _hZ hq
  have hsq : IsPullback (pullback.fst p q).left (pullback.snd p q).left p.left q.left :=
    (IsPullback.of_hasPullback p q).map (Over.forget S)
  have : IsOpenImmersion (pullback.fst p q).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip hq
  exact B.contains_of_mono (pullback.fst p q).left hY

omit [IsLocallyNoetherian S] in
/-- A sheaf for the étale coverings of `Sch/S` is a sheaf for its Zariski coverings. -/
theorem isCoveringSheaf_zariski_of_etale {G : (Over S)ᵒᵖ ⥤ Type w}
    (hG : IsCoveringSheaf.{w, u, u} .etale G) : IsCoveringSheaf.{w, u, u} .zariski G := by
  intro ι X Y f hf
  rw [ofArrows_mem_coveringPrecoverage_iff] at hf
  refine hG X Y f ?_
  rw [ofArrows_mem_coveringPrecoverage_iff]
  exact ⟨hf.1, fun i => by
    have : IsOpenImmersion (f i).left := hf.2 i
    exact (inferInstance : Etale (f i).left)⟩

include hFs hFl in
/-- **The extension is a sheaf for the Zariski coverings by objects of the site.** -/
theorem isCoveringSheafOnSubcategory_extensionToBigFppfOver :
    IsCoveringSheafOnSubcategory.{max w (u + 1), u, u} .zariski (IsContainedOver B (S := S))
      ((toBigFppfOver B hS).op ⋙ extensionToBigFppfOver B hS F) :=
  isCoveringSheafOnSubcategory_of_isCoveringSheaf .zariski
    (hasCoveringPullbacks_zariski_isContainedOver (B := B))
    (isCoveringSheaf_zariski_of_etale
      (isLimitPreservingSheaf_extension_locallyNoetherian hFs hFl).1)

omit [IsLocallyNoetherian S] in
/-- **The objects of `Sch/S` contained in `B` contain the fibre products of two of them.** -/
theorem hasCoveringPullbacks_etale_isContainedOver :
    HasCoveringPullbacks .etale (IsContainedOver B (S := S)) := by
  intro X Y Z p q hY hZ _hq
  have hsq : IsPullback (pullback.fst p q).left (pullback.snd p q).left p.left q.left :=
    (IsPullback.of_hasPullback p q).map (Over.forget S)
  change (pullback p q).left.size < B.cutoff
  rw [Scheme.size_congr hsq.isoPullback]
  exact Scheme.size_pullback_lt p.left q.left hY hZ

include hFs hFl in
/-- The extension on `Sch/S` is a sheaf for the étale coverings indexed by types of the universe
of the objects of `Sch/S`. -/
theorem isCoveringSheaf_etale_extension_locallyNoetherian :
    IsCoveringSheaf.{max w (u + 1), u, u + 1} .etale
      (extension (IsContainedLocallyNoetherianOver B (S := S))
        ((toLocallyNoetherianOver B hS).op ⋙ F)) := by
  intro ι X Y f hf
  exact isCoveringSheaf_extension_of_isStandardAffineSheafOnSubcategory .etale _ _
    (hasAffineOpens_isContainedLocallyNoetherianOver B)
    (hasFinitePresentationAffines_isContainedLocallyNoetherianOver B hS)
    (isZariskiSheafOnSubcategory_of_isSheafFor B hS hFs)
    (preservesAffineLimitsOnSubcategory_of_limitPreserving_locallyNoetherian B hS hFl)
    (isStandardAffineSheafOnSubcategory_of_isCoveringSheafOnSubcategory .etale
      (isCoveringSheafOnSubcategory_etale_of_isSheafFor B S hS hFs)) X Y f hf

include hFs hFl in
/-- **The extension is a sheaf for the big étale topology of `S`.** -/
theorem isSheaf_etaleTopology_extensionToBigFppfOver :
    Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) (extensionToBigFppfOver B hS F) := by
  obtain ⟨-, -, h₃, h₄⟩ := etalePrecoverage_hasIsos_and_isStable B
  rw [show etaleTopology B = (etalePrecoverage B).toGrothendieck from rfl,
    over_toGrothendieck_eq_toGrothendieck_comap_forget, isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  have hG : IsCoveringSheafOnSubcategory.{max w (u + 1), u, u + 1} .etale
      (IsContainedOver B (S := S)) ((IsContainedOver B (S := S)).ι.op ⋙
        extension (IsContainedLocallyNoetherianOver B (S := S))
          ((toLocallyNoetherianOver B hS).op ⋙ F)) :=
    isCoveringSheafOnSubcategory_of_isCoveringSheaf .etale
      (hasCoveringPullbacks_etale_isContainedOver (B := B))
      (isCoveringSheaf_etale_extension_locallyNoetherian hFs hFl)
  let Φ := fromBigFppfOver B hS
  have hΦ : Φ.FullyFaithful := (bigFppfOverEquivalence B hS).fullyFaithfulFunctor
  have : Φ.EssSurj := (bigFppfOverEquivalence B hS).essSurj_functor
  change Presieve.IsSheafFor (Φ.op ⋙ ((IsContainedOver B (S := S)).ι.op ⋙
    extension (IsContainedLocallyNoetherianOver B (S := S))
      ((toLocallyNoetherianOver B hS).op ⋙ F))) (Presieve.ofArrows E.X E.f)
  apply Presieve.isSheafFor_ofArrows_op_comp_of_fullyFaithful hΦ
  refine hG (Φ.obj T) (fun i => Φ.obj (E.X i)) (fun i => Φ.map (E.f i)) ?_
  rw [Precoverage.mem_comap_iff, etalePrecoverage_eq_comap, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows, Presieve.map_ofArrows] at hR
  rw [ofArrows_mem_coveringPrecoverage_iff]
  exact (Scheme.ofArrows_mem_precoverage_iff
    (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).1 hR

end ExtendingFunctors

end AlgebraicGeometry
