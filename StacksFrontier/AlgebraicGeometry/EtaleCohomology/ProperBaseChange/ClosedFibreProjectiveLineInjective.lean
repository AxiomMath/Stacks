module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedFibreTwoChartVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AffineClosedInjectiveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic

/-!
# Injective sheaves of `ℤ/ℓℤ`-modules are acyclic on the closed fibre of `P¹`

Let `A` be a henselian local ring, `X = P¹_A`, `X₀` its closed fibre and `𝓘` an injective sheaf
of `ℤ/ℓℤ`-modules on `X_étale`. Then `H^q(X₀, 𝓘|_{X₀}) = 0` for every `q > 0`. This is the
vanishing which the proof of [Stacks, Tag 0A5H] establishes for `P¹_A`.

## Main results

* `subsingleton_H_of_isDenseSubsite` and
  `subsingleton_H_sheafPushforwardContinuous_of_isDenseSubsite`, in the namespace
  `Stacks.Cohomology.DenseSubsiteTransport` — vanishing of the cohomology of an arbitrary abelian
  sheaf moves between a dense subsite and the larger site.
* `Stacks.EtaleCohomology.ConstantTransport.subsingleton_H'_opensToSite_of_subsingleton_H` —
  cohomology over an open subscheme, read on the small étale site of the ambient scheme, from the
  cohomology of the restriction.
* `Stacks.EtaleCohomology.exists_comp_eq_of_adjunction` — injectivity among the objects killed
  by `n` passes to the right adjoint of an additive functor preserving monomorphisms.
* `Stacks.EtaleCohomology.subsingleton_H'_preimage_of_injective` — vanishing over the trace on a
  closed subscheme of an affine open.
* `Stacks.EtaleCohomology.subsingleton_H_closedFibre_projectiveLine_of_injective` — the
  vanishing on the closed fibre of `P¹_A`.

## References

* [Stacks Project, Tag 0A5H](https://stacks.math.columbia.edu/tag/0A5H)
* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.ZModSheaf

universe w w' v₁ u₁ v₂ u₂ a u

namespace Stacks.Cohomology.DenseSubsiteTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
  {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))

include hTC hTD

/-- **Cohomology does not change on a dense subsite**, read from the subsite: if `G : C ⥤ D`
exhibits `(C, J)` as a dense subsite of `(D, K)` and carries a terminal object to a terminal
object, the vanishing of `H^q` of the restriction of an abelian sheaf `F` on `(D, K)` gives the
vanishing of `H^q(F)`. -/
theorem subsingleton_H_of_isDenseSubsite (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{w}
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) q)) :
    Subsingleton (Sheaf.H.{w'} F q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : ∀ I : Type a, HasLimitsOfShape (Discrete I) (Cᵒᵖ ⥤ AddCommGrpCat.{a}) :=
    fun I => have : HasLimitsOfShape (Discrete I) AddCommGrpCat.{a} :=
      AddCommGrpCat.hasLimitsOfShape
    functorCategoryHasLimitsOfShape
  have : HasFiniteProducts (Sheaf J AddCommGrpCat.{a}) := Abelian.has_finite_products
  have : HasBinaryProducts (Sheaf J AddCommGrpCat.{a}) := hasLimitsOfShape_discrete _ _
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.functor :=
    (E.symm.toAdjunction.rightAdjoint_preservesLimits (G := E.functor)).preservesLimitsOfShape
  have := E.toAdjunction.isLeftAdjoint
  have : E.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app (AddCommGrpCat.of (ULift.{a} ℤ))) q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ))) F q h)

/-- **Cohomology does not change on a dense subsite**, read from the larger site: the vanishing
of `H^q(F)` for an abelian sheaf `F` on `(D, K)` gives the vanishing of `H^q` of its
restriction to `(C, J)`. -/
theorem subsingleton_H_sheafPushforwardContinuous_of_isDenseSubsite
    (F : Sheaf K AddCommGrpCat.{a}) (q : ℕ) (h : Subsingleton (Sheaf.H.{w'} F q)) :
    Subsingleton (Sheaf.H.{w}
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) q) := by
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : ∀ I : Type a, HasLimitsOfShape (Discrete I) (Dᵒᵖ ⥤ AddCommGrpCat.{a}) :=
    fun I => have : HasLimitsOfShape (Discrete I) AddCommGrpCat.{a} :=
      AddCommGrpCat.hasLimitsOfShape
    functorCategoryHasLimitsOfShape
  have : HasFiniteProducts (Sheaf K AddCommGrpCat.{a}) := Abelian.has_finite_products
  have : HasBinaryProducts (Sheaf K AddCommGrpCat.{a}) := hasLimitsOfShape_discrete _ _
  have : PreservesLimitsOfShape (Discrete WalkingPair) E.symm.functor :=
    (E.toAdjunction.rightAdjoint_preservesLimits (G := E.symm.functor)).preservesLimitsOfShape
  have := E.symm.toAdjunction.isLeftAdjoint
  have : E.symm.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : E.symm.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₀ : Subsingleton (Abelian.Ext.{w'}
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.symm.inverse.obj (E.inverse.obj F)) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target (E.counitIso.app F).symm q h
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    ((equivCommuteConstant' J AddCommGrpCat.{a} K G hTC hTD).app
      (AddCommGrpCat.of (ULift.{a} ℤ))).symm q
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence E.symm
      ((constantSheaf K AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift.{a} ℤ)))
      (E.inverse.obj F) q h₀)

end Stacks.Cohomology.DenseSubsiteTransport

namespace Stacks.EtaleCohomology.ConstantTransport

open AlgebraicGeometry.Scheme.Etale

variable (Y : Scheme.{u})

/-- An abelian sheaf on Mathlib's small étale site of `Y`, read on its one-universe model. -/
abbrev toMayerVietoris :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1} :=
  (AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (MayerVietoris.topology Y) Y.smallEtaleTopology

/-- The identity of `Y` is terminal in the small étale site of `Y`. -/
private def isTerminal_down_self :
    IsTerminal ((AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale).obj (MayerVietoris.self Y)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

/-- **Vanishing passes from the one-universe model of the small étale site to Mathlib's**, for an
arbitrary abelian sheaf. -/
theorem subsingleton_H_of_subsingleton_H_toMayerVietoris
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} ((toMayerVietoris Y).obj F) q)) :
    Subsingleton (Sheaf.H.{u + 1} F q) :=
  Stacks.Cohomology.DenseSubsiteTransport.subsingleton_H_of_isDenseSubsite _ _
    (AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale) (MayerVietoris.selfIsTerminal Y)
    (isTerminal_down_self Y) F q h

/-- **Vanishing passes from Mathlib's small étale site to its one-universe model**, for an
arbitrary abelian sheaf. -/
theorem subsingleton_H_toMayerVietoris_of_subsingleton_H
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} F q)) :
    Subsingleton (Sheaf.H.{u + 1} ((toMayerVietoris Y).obj F) q) :=
  Cohomology.DenseSubsiteTransport.subsingleton_H_sheafPushforwardContinuous_of_isDenseSubsite
    _ _ (AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale) (MayerVietoris.selfIsTerminal Y)
    (isTerminal_down_self Y) F q h

variable (S : Scheme.{u}) (U : S.Opens)

/-- **Cohomology over an open subscheme from the cohomology of the restriction.** For an abelian
sheaf `F` on the one-universe small étale site of `S` and an open `U ⊆ S`, the vanishing of the
global cohomology of the restriction of `F` to the small étale site of `U` gives the vanishing of
the cohomology of `F` over `U`, read as an object of the small étale site of `S` (Stacks 03YU,
statement 2). -/
theorem subsingleton_H'_opensToSite_of_subsingleton_H
    (F : Sheaf (MayerVietoris.topology S) AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1}
      (((opensInclusion S U).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S)).obj F) q)) :
    Subsingleton (Sheaf.H'.{u + 1} F q ((MayerVietoris.opensToSite S).obj U)) := by
  have : ∀ P : (MayerVietoris.Site U.toScheme)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (opensInclusion S U).op.HasPointwiseRightKanExtension P :=
    fun P => Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  have h1 := (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'
      (MayerVietoris.topology U.toScheme) _ q _ (MayerVietoris.selfIsTerminal U.toScheme)).1 h
  have iso := (Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso
        (MayerVietoris.topology U.toScheme) (MayerVietoris.topology S) (opensInclusion S U)
        (MayerVietoris.self U.toScheme) q).app F ≪≫
      (F.cohomologyPresheaf q).mapIso (opensInclusionSelfIso S U).op.symm
  exact @Equiv.subsingleton _ _ iso.symm.addCommGroupIsoToAddEquiv.toEquiv h1

end Stacks.EtaleCohomology.ConstantTransport

namespace Stacks.EtaleCohomology

/-- An additive functor preserves the vanishing of `n • 𝟙 P`. -/
private theorem zsmul_id_map_eq_zero {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (F : C ⥤ D) [F.Additive] {n : ℤ} {P : C}
    (h : n • 𝟙 P = 0) : n • 𝟙 (F.obj P) = 0 := by
  rw [← F.map_id, ← Functor.map_zsmul, h, F.map_zero]

/-- **Injectivity among the objects killed by `n` passes to a right adjoint.** Let `L ⊣ R` with
`L` additive and preserving monomorphisms, and let `I` be an object such that every map into `I`
from an object killed by `n` extends along a monomorphism into an object killed by `n`. Then
`R I` has the same property. -/
theorem exists_comp_eq_of_adjunction {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [L.PreservesMonomorphisms] (n : ℤ) (I : D)
    (hext : ∀ {P Q : D}, n • 𝟙 P = 0 → n • 𝟙 Q = 0 → ∀ (m : P ⟶ Q) [Mono m] (g : P ⟶ I),
      ∃ h : Q ⟶ I, m ≫ h = g)
    {P Q : C} (hP : n • 𝟙 P = 0) (hQ : n • 𝟙 Q = 0) (m : P ⟶ Q) [Mono m] (g : P ⟶ R.obj I) :
    ∃ h : Q ⟶ R.obj I, m ≫ h = g := by
  obtain ⟨h, hh⟩ := hext (zsmul_id_map_eq_zero L hP) (zsmul_id_map_eq_zero L hQ) (L.map m)
    ((adj.homEquiv P I).symm g)
  refine ⟨adj.homEquiv Q I h, ?_⟩
  rw [← Adjunction.homEquiv_naturality_left, hh, Equiv.apply_symm_apply]

/-- **Vanishing over the trace of an affine open on a closed subscheme.** Let `i : Z ⟶ X` be a
closed immersion, `V ⊆ X` an affine open, `ℓ > 0` and `𝓘` an injective sheaf of `ℤ/ℓℤ`-modules
on `X_étale`. Then the cohomology of `𝓘|_Z` over `Z ∩ V`, read on the small étale site of `Z`,
vanishes in every positive degree. -/
theorem subsingleton_H'_preimage_of_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (ℓ : ℕ) [NeZero ℓ]
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    (V : X.Opens) (hV : IsAffineOpen V) (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H'.{u + 1} ((ConstantTransport.toMayerVietoris Z).obj
      ((etaleAbelianInverseImage.{u, 0} i).obj ((SheafOfModules.toSheaf _).obj J))) n
      ((MayerVietoris.opensToSite Z).obj (i ⁻¹ᵁ V))) := by
  have : IsAffine V := hV
  let W := i ⁻¹ᵁ V
  let iV : W.toScheme ⟶ V.toScheme := i ∣_ V
  have : IsClosedImmersion iV := IsZariskiLocalAtTarget.restrict ‹_› V
  let TJ := (SheafOfModules.toSheaf _).obj J
  let F := (etaleAbelianInverseImage.{u, 0} i).obj TJ
  let I := (etaleRestriction.{u, 0} V.ι).obj TJ
  have hTJ : ((ℓ : ℤ) • 𝟙 TJ) = 0 := by
    apply Sheaf.hom_ext
    ext U x
    rw [zsmul_app_apply]
    change ((ℓ : ℤ) • x) = 0
    rw [natCast_zsmul]
    exact nsmul_toSheaf_eq_zero.{u + 1, u + 1} X.smallEtaleTopology ℓ J U x
  have hI : ((ℓ : ℤ) • 𝟙 I) = 0 := zsmul_id_map_eq_zero (etaleRestriction.{u, 0} V.ι) hTJ
  have hext : ∀ {P Q : Sheaf V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}},
      ((ℓ : ℤ) • 𝟙 P) = 0 → ((ℓ : ℤ) • 𝟙 Q) = 0 → ∀ (m : P ⟶ Q) [Mono m] (g : P ⟶ I),
        ∃ h : Q ⟶ I, m ≫ h = g := fun hP hQ m _ g =>
    exists_comp_eq_of_adjunction (extensionByZeroAdj.{u, 0} V.ι) (ℓ : ℤ) TJ
      (fun hP' hQ' m' _ g' => exists_comp_eq_of_injective_toSheaf ℓ J
        (nsmul_eq_zero_of_zsmul_id_eq_zero ℓ hP') (nsmul_eq_zero_of_zsmul_id_eq_zero ℓ hQ') m' g')
      hP hQ m g
  let e : (etaleRestriction.{u, 0} W.ι).obj F ≅ (etaleAbelianInverseImage.{u, 0} iV).obj I :=
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} W.ι).app F).symm ≪≫
      ((etaleAbelianInverseImageCompIso'.{u, 0} W.ι i (W.ι ≫ i) rfl).app TJ).symm ≪≫
      (etaleAbelianInverseImageCompIso'.{u, 0} iV V.ι (W.ι ≫ i)
        (morphismRestrict_ι i V).symm).app TJ ≪≫
      (etaleAbelianInverseImage.{u, 0} iV).mapIso
        ((etaleAbelianInverseImageRestrictionIso.{u, 0} V.ι).app TJ)
  exact ConstantTransport.subsingleton_H'_opensToSite_of_subsingleton_H _ _ _ _
    (ConstantTransport.subsingleton_H_toMayerVietoris_of_subsingleton_H _ _ n
      (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target e.symm n
        (subsingleton_H_closed_of_isAffine_of_torsion_extension iV ℓ I hI hext n hn)))

/-- **Stacks Project, Tag 0A5H.** Let `A` be a henselian local ring, `X = P¹_A` with closed
fibre `X₀`, `ℓ` a prime number and `𝓘` an injective sheaf of `ℤ/ℓℤ`-modules on `X_étale`. Then
`H^q_ét(X₀, 𝓘|_{X₀}) = 0` for every `q > 0`. -/
theorem subsingleton_H_closedFibre_projectiveLine_of_injective
    (ℓ : ℕ) (hℓ : ℓ.Prime) (A : Type u) [CommRing A] [HenselianLocalRing A]
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
      (ProjectiveSpace 1 (Spec (.of A))).smallEtaleTopology ℓ)) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (closedFibreInclusion A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)))).obj
        ((SheafOfModules.toSheaf _).obj J)) q) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let X := projectiveSpaceOverRing 1 (.of A)
  let p : X ⟶ Spec (.of A) := X ↘ Spec (.of A)
  let i := closedFibreInclusion A p
  have : IsClosedImmersion i := isClosedImmersion_closedFibreInclusion A p
  let J' : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ) := J
  have : Injective J' := ‹Injective J›
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · obtain rfl : q = 1 := by omega
    exact subsingleton_H_one_closedFibre_of_injective A p ℓ J'
  have hstd : ∀ k : Fin 2, IsAffineOpen (ProjectiveSpace.standardOpen 1 (Spec (.of A)) k) :=
    ProjectiveSpace.isAffineOpen_standardOpen 1 (Spec (.of A))
  have : X.IsSeparated := projectiveSpaceOver.isSeparated 1 (Spec (.of A))
  have : IsSeparated (terminal.from X) := Scheme.IsSeparated.isSeparated_terminal_from
  have : IsClosedImmersion (pullback.diagonal (terminal.from X)) :=
    IsSeparated.isClosedImmersion_diagonal
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  exact ConstantTransport.subsingleton_H_of_subsingleton_H_toMayerVietoris _ _ q
    (subsingleton_H_closedFibre_projectiveLine_of_charts_acyclic A _
      (fun n hn => subsingleton_H'_preimage_of_injective i ℓ J' _ ((hstd 0).inf (hstd 1)) n hn)
      (fun k n hn => subsingleton_H'_preimage_of_injective i ℓ J' _ (hstd k) n hn) q hq2)

end Stacks.EtaleCohomology

end
