module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.AffineExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# When a coherent adic system on the open complement is algebraizable

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec A`, the closed subscheme `Y = V(I)` and the open complement `U = X ∖ V(𝔞)`. A coherent
`I`-adic system `(F_n)` on `U` can be presented in several ways, and this file proves that four of
them agree and that they imply extendability to `X`:

* it lies in the essential image of the completion functor of `U`;
* it is the completion of a coherent module on some open neighbourhood of `U ∩ Y` inside `U`;
* it is the completion of a coherent module on `U` that extends to `X`;
* it is the restriction to `U` of the completion of a coherent module on `X`;

and any of these implies that `(F_n)` extends to a coherent `I`-adic system on `X`.

The equivalences rest on two inputs. Completion commutes with restriction to an open
(`Stacks.Algebraization.completionRestrictOpenIso`), which makes the passage between `X`, `U` and a
smaller neighbourhood `V` formal. And every coherent module on an open of the affine Noetherian
`X` is the restriction of a coherent module on `X`, which is the affine case of [Stacks, Tag 0G41]
part (2), `Stacks.FundamentalGroup.ExtendedEtaleFold.exists_isCoherent_restrict_iso`; this is what
lets a module defined only near the closed locus be spread out.

The step from a neighbourhood `V` of `U ∩ Y` back to `U` uses a third observation: every term of a
coherent adic system along `I 𝒪_U` is annihilated by a power of that ideal, hence is supported on
`U ∩ Y ⊆ V`, and restriction to `V` is an equivalence onto the modules supported on `V`, with
quasi-inverse the extension by zero. So an isomorphism of systems over `V` is already an
isomorphism over `U`.

## Main definitions

* `Stacks.Algebraization.IsCompletionNearClosed` — condition (3) of Stacks 0EIL.
* `Stacks.Algebraization.IsCompletionOfRestriction` — condition (4).
* `Stacks.Algebraization.IsRestrictionOfCompletion` — condition (5).

## Main results

* `Stacks.Algebraization.isCompletion_iff_nearClosed` — conditions (2) and (3) agree.
* `Stacks.Algebraization.isCompletion_iff_ofRestriction` — conditions (2) and (4) agree.
* `Stacks.Algebraization.isCompletionOfRestriction_iff_isRestrictionOfCompletion` — conditions (4)
  and (5) agree.
* `Stacks.Algebraization.extendsToX_of_isRestrictionOfCompletion` — condition (5) implies
  condition (6), `Stacks.Algebraization.ExtendsToX`.
* `Stacks.Algebraization.supportedDiagramIsoOfRestrictIso` — two `ℕᵒᵖ`-indexed diagrams of modules
  supported on an open `V` are isomorphic as soon as their restrictions to `V` are.
* `Stacks.Algebraization.exists_isCoherent_restrict_iso_of_opens` — a coherent module on an open
  of an open of an affine locally Noetherian scheme extends to the intermediate open.

## Implementation notes

Tag 0EIL asserts the equivalence of six conditions. The remaining implication — that
extendability to `X` implies condition (5) when `A` is `I`-adically complete — is proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/AffineExistence.lean`, since it
needs the essential surjectivity of the completion functor on the affine scheme `X`.

The ideal on `U` is written as `S.Yι.ker.comap S.U.ι`, the pullback of the kernel ideal sheaf of
`Y ⟶ X`, which is the spelling `Stacks.Algebraization.ExtendsToX` uses;
`Stacks.Algebraization.idealOnOpen` is the same ideal presented through the top ideal sheaf of `X`.

## References

* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- Every term of a coherent adic system along `I` is supported on the closed set cut out
by `I`: the term is annihilated by a power of `I`. -/
public theorem supp_coherentAdicSystem_obj_subset {X : Scheme.{u}} [IsNoetherian X]
    {I : X.IdealSheafData} (F : Stacks.Coherent.CoherentAdicSystems I) (n : ℕ) :
    SheafOfModules.supp (F.obj.obj (op n)) ⊆ I.support := by
  have hcoh : (F.obj.obj (op n)).IsCoherent := F.property.1 n
  exact (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset
    (F.obj.obj (op n)) I).mp ⟨n + 1, F.property.2.1 n⟩

/-- The closed set cut out by `I 𝒪_U` is the preimage of `Y` in the open `U`. -/
public theorem support_ker_comap_eq (S : AlgebraizationSituation.{u}) :
    (S.Yι.ker.comap S.U.ι).support = S.U.ι.base ⁻¹' Set.range S.Yι.base := by
  rw [Scheme.IdealSheafData.support_comap]
  change S.U.ι.base ⁻¹' (S.Yι.ker.support : Set S.X) =
    S.U.ι.base ⁻¹' Set.range S.Yι.base
  rw [Scheme.Hom.support_ker, S.Yι.isClosedEmbedding.isClosed_range.closure_eq]

/-- Restriction to an open subspace of a ringed space, as it appears in the extension-by-zero
adjunction, is Mathlib's restriction along the inclusion of an open subscheme. -/
public theorem jStar_eq_restrictFunctor {X : Scheme.{u}} (V : X.Opens) :
    ExtensionByZeroModules.jStar V X.ringCatSheaf =
      Scheme.Modules.restrictFunctor V.ι := by
  unfold ExtensionByZeroModules.jStar Scheme.Modules.restrictFunctor
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- For a module supported on `V`, the counit `j_!(M|_V) ⟶ M` of the extension-by-zero
adjunction is an isomorphism. -/
public theorem isIso_jShriekAdjunction_counit_app_of_supp {X : Scheme.{u}} (V : X.Opens)
    (M : X.Modules) (hM : SheafOfModules.supp M ⊆ (V : Set X)) :
    IsIso ((ExtensionByZeroModules.jShriekAdjunction V X.ringCatSheaf).counit.app M) :=
  ExtensionByZeroModules.counit_isIso_of_stalk_isZero V X.ringCatSheaf M fun x hx =>
    AddCommGrpCat.isZero_iff_subsingleton.mpr <| not_nontrivial_iff_subsingleton.mp fun hn =>
      hx (hM ((SheafOfModules.mem_supp_iff_nontrivial_stalk M x).mpr hn))

/-- **Two diagrams of modules supported on an open `V` are isomorphic as soon as their
restrictions to `V` are.** Restriction to `V` is fully faithful on modules supported on `V`,
with quasi-inverse the extension by zero `j_!`, and the counit of `j_! ⊣ j^*` is a natural
isomorphism there. -/
public noncomputable def supportedDiagramIsoOfRestrictIso {X : Scheme.{u}}
    (V : X.Opens) {A B : ℕᵒᵖ ⥤ X.Modules}
    (hA : ∀ i, SheafOfModules.supp (A.obj i) ⊆ (V : Set X))
    (hB : ∀ i, SheafOfModules.supp (B.obj i) ⊆ (V : Set X))
    (e : A ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      B ⋙ Scheme.Modules.restrictFunctor V.ι) : A ≅ B := by
  let j := ExtensionByZeroModules.jStar V X.ringCatSheaf
  let k := ExtensionByZeroModules.jShriek V X.ringCatSheaf
  let c := (ExtensionByZeroModules.jShriekAdjunction V X.ringCatSheaf).counit
  have e' : A ⋙ j ≅ B ⋙ j := by
    change A ⋙ ExtensionByZeroModules.jStar V X.ringCatSheaf ≅
      B ⋙ ExtensionByZeroModules.jStar V X.ringCatSheaf
    rw [jStar_eq_restrictFunctor]
    exact e
  let a : (A ⋙ j) ⋙ k ≅ A := NatIso.ofComponents
    (fun i => by
      have := isIso_jShriekAdjunction_counit_app_of_supp V (A.obj i) (hA i)
      exact asIso (c.app (A.obj i)))
    (by
      intro i l g
      exact c.naturality (A.map g))
  let b : (B ⋙ j) ⋙ k ≅ B := NatIso.ofComponents
    (fun i => by
      have := isIso_jShriekAdjunction_counit_app_of_supp V (B.obj i) (hB i)
      exact asIso (c.app (B.obj i)))
    (by
      intro i l g
      exact c.naturality (B.map g))
  exact a.symm ≪≫ Functor.isoWhiskerRight e' k ≪≫ b

/-- **A coherent module on an open of an open of an affine locally Noetherian scheme extends to
that open.** The composite of the two inclusions is an open immersion into the affine scheme, so
the module extends to the whole affine scheme by
`Stacks.FundamentalGroup.ExtendedEtaleFold.exists_isCoherent_restrict_iso`, and the extension is
then restricted to the intermediate open. -/
public theorem exists_isCoherent_restrict_iso_of_opens {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsAffine X] (U : X.Opens) (V : U.toScheme.Opens)
    (G : V.toScheme.Modules) [_root_.SheafOfModules.IsCoherent G] :
    ∃ E : U.toScheme.Modules, _root_.SheafOfModules.IsCoherent E ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj E ≅ G) := by
  let W : X.Opens := U.ι ''ᵁ V
  let φ : V.toScheme ≅ W.toScheme := U.ι.isoImage V
  have hφ : φ.hom ≫ W.ι = V.ι ≫ U.ι := Scheme.Hom.isoImage_hom_ι U.ι V
  have hGq : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  let G' : W.toScheme.Modules := (Scheme.Modules.pushforward φ.hom).obj G
  have hG'c : _root_.SheafOfModules.IsCoherent G' :=
    Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite φ.hom G
  obtain ⟨E, hEc, ⟨e⟩⟩ :=
    Stacks.FundamentalGroup.ExtendedEtaleFold.exists_isCoherent_restrict_iso W G'
  have hEr : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.restrictFunctor U.ι).obj E) :=
    @isCoherent_restrict_of_isOpenImmersion X U.toScheme U.ι inferInstance inferInstance E hEc
  refine ⟨(Scheme.Modules.restrictFunctor U.ι).obj E, hEr, ⟨?_⟩⟩
  calc (Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.restrictFunctor U.ι).obj E)
      ≅ E.restrict (V.ι ≫ U.ι) := ((Scheme.Modules.restrictFunctorComp V.ι U.ι).app E).symm
    _ ≅ E.restrict (φ.hom ≫ W.ι) := (Scheme.Modules.restrictFunctorCongr hφ.symm).app E
    _ ≅ (E.restrict W.ι).restrict φ.hom := (Scheme.Modules.restrictFunctorComp φ.hom W.ι).app E
    _ ≅ G'.restrict φ.hom := (Scheme.Modules.restrictFunctor φ.hom).mapIso e
    _ ≅ G := (Scheme.Modules.restrictFunctorAdjCounitIso φ.hom).app G

/-! ### The algebraization conditions of Stacks 0EIL -/

/-- **Condition (3) of Stacks 0EIL.** The system is the completion of a coherent module on some
open neighbourhood of `U ∩ Y` inside `U`. -/
public def IsCompletionNearClosed (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) : Prop :=
  ∃ V : S.U.toScheme.Opens,
    (S.U.ι.base ⁻¹' Set.range S.Yι.base) ⊆ (V : Set S.U.toScheme) ∧
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
        Nonempty ((((completionFunctor V.toScheme
          ((S.Yι.ker.comap S.U.ι).comap V.ι)).obj G).obj) ≅
          (F.obj ⋙ Scheme.Modules.restrictFunctor V.ι))

/-- **Condition (4) of Stacks 0EIL.** The system is the completion of a coherent module on `U`
which is the restriction of a coherent module on `X`. -/
public def IsCompletionOfRestriction (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) : Prop :=
  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules S.X.ringCatSheaf,
    ∃ H : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf,
      Nonempty ((Scheme.Modules.restrictFunctor S.U.ι).obj G.obj ≅ H.obj) ∧
        Nonempty ((completionFunctor S.U.toScheme
          (S.Yι.ker.comap S.U.ι)).obj H ≅ F)

/-- **Condition (5) of Stacks 0EIL.** The system is the restriction to `U` of the completion of a
coherent module on `X`. -/
public def IsRestrictionOfCompletion (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) : Prop :=
  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules S.X.ringCatSheaf,
    Nonempty (((completionFunctor S.X S.Yι.ker).obj G).obj ⋙
      Scheme.Modules.restrictFunctor S.U.ι ≅ F.obj)

/-- **Stacks 0EIL, conditions (2) and (3) are equivalent.** A coherent adic system on `U` is the
completion of a coherent module on `U` exactly when it is the completion of a coherent module on
some open neighbourhood of `U ∩ Y` in `U`.

One direction takes the neighbourhood to be `U` itself. For the other, a coherent module on the
neighbourhood `V` extends to `U`, and the two systems — the completion of the extension and the
given one — are then isomorphic over `V`; every term of either is annihilated by a power of the
ideal and so is supported inside `V`, and restriction to `V` is fully faithful on modules
supported there, so the isomorphism over `V` comes from an isomorphism over `U`. -/
@[stacks 0EIL "completion iff near the closed subscheme"]
public theorem isCompletion_iff_nearClosed (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage F ↔
      IsCompletionNearClosed S F := by
  let I := S.Yι.ker.comap S.U.ι
  refine ⟨fun ⟨G, ⟨e⟩⟩ => ?_, fun ⟨V, hV, G, ⟨e⟩⟩ => ?_⟩
  · refine ⟨⊤, ?_, restrictCoherentModules (⊤ : S.U.toScheme.Opens).ι G, ⟨?_⟩⟩
    · simp
    · exact (completionRestrictOpenIso (⊤ : S.U.toScheme.Opens).ι I G).symm ≪≫
        Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso e)
          (Scheme.Modules.restrictFunctor (⊤ : S.U.toScheme.Opens).ι)
  · have hNoeth : NoetherianSpace S.U.toScheme := NoetherianSpace.set (S.U : Set S.X)
    have hN : IsNoetherian S.U.toScheme := ⟨⟩
    have hGc : _root_.SheafOfModules.IsCoherent G.obj := G.property
    obtain ⟨E, hEc, ⟨eEG⟩⟩ := exists_isCoherent_restrict_iso_of_opens S.U V G.obj
    let H : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf :=
      ⟨E, hEc⟩
    let eHV : restrictCoherentModules V.ι H ≅ G := ObjectProperty.isoMk _ eEG
    let A := (completionFunctor S.U.toScheme I).obj H
    have eV : A.obj ⋙ Scheme.Modules.restrictFunctor V.ι ≅
        F.obj ⋙ Scheme.Modules.restrictFunctor V.ι :=
      completionRestrictOpenIso V.ι I H ≪≫
        (ObjectProperty.ι _).mapIso
          ((completionFunctor V.toScheme (I.comap V.ι)).mapIso eHV) ≪≫ e
    have hsupp : ∀ (C : Stacks.Coherent.CoherentAdicSystems I) (i : ℕᵒᵖ),
        SheafOfModules.supp (C.obj.obj i) ⊆ (V : Set S.U.toScheme) := fun C i =>
      (supp_coherentAdicSystem_obj_subset C i.unop).trans
        ((support_ker_comap_eq S).le.trans hV)
    exact ⟨H, ⟨ObjectProperty.isoMk _ (supportedDiagramIsoOfRestrictIso V (hsupp A) (hsupp F) eV)⟩⟩

/-- **Stacks 0EIL, conditions (2) and (4) are equivalent.** A coherent adic system on `U` is the
completion of a coherent module on `U` exactly when it is the completion of one that extends to a
coherent module on `X`.

`X` is affine and Noetherian, so every coherent module on the open `U` is the restriction of a
coherent module on `X`; the converse direction forgets the extension. -/
@[stacks 0EIL "completion iff completion of a restriction"]
public theorem isCompletion_iff_ofRestriction (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage F ↔
      IsCompletionOfRestriction S F := by
  refine ⟨fun ⟨G, ⟨e⟩⟩ => ?_, fun ⟨_, H, _, ⟨e⟩⟩ => ⟨H, ⟨e⟩⟩⟩
  have hGc : _root_.SheafOfModules.IsCoherent G.obj := G.property
  obtain ⟨G', hG'c, ⟨e'⟩⟩ :=
    Stacks.FundamentalGroup.ExtendedEtaleFold.exists_isCoherent_restrict_iso S.U G.obj
  exact ⟨⟨G', hG'c⟩, G, ⟨e'⟩, ⟨e⟩⟩

/-- **Stacks 0EIL, conditions (4) and (5) are equivalent.** Being the completion of a module
restricted from `X` is the same as being the restriction of a completion on `X`, because
completion commutes with restriction to an open. -/
@[stacks 0EIL "the two restriction conditions agree"]
public theorem isCompletionOfRestriction_iff_isRestrictionOfCompletion
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι)) :
    IsCompletionOfRestriction S F ↔ IsRestrictionOfCompletion S F := by
  refine ⟨fun ⟨G, H, ⟨eGH⟩, ⟨eHF⟩⟩ => ⟨G, ⟨?_⟩⟩, fun ⟨G, ⟨e⟩⟩ =>
    ⟨G, restrictCoherentModules S.U.ι G, ⟨Iso.refl _⟩,
      ⟨ObjectProperty.isoMk _ ((completionRestrictOpenIso S.U.ι S.Yι.ker G).symm ≪≫ e)⟩⟩⟩
  exact completionRestrictOpenIso S.U.ι S.Yι.ker G ≪≫
    (ObjectProperty.ι _).mapIso
      ((completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).mapIso
        (ObjectProperty.isoMk _ eGH)) ≪≫ (ObjectProperty.ι _).mapIso eHF

/-- **Stacks 0EIL, condition (5) implies condition (6).** A system that is the restriction of a
completion on `X` extends to `X`: the completion itself is the extension. -/
@[stacks 0EIL "restriction of a completion extends to X"]
public theorem extendsToX_of_isRestrictionOfCompletion (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (S.Yι.ker.comap S.U.ι))
    (h : IsRestrictionOfCompletion S F) : ExtendsToX S F := by
  obtain ⟨G, ⟨e⟩⟩ := h
  exact ⟨(completionFunctor S.X S.Yι.ker).obj G, ⟨e⟩⟩

end Stacks.Algebraization

end
