module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.Main
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Embedding a constructible sheaf of sets into finite direct images of constant sheaves

Let `X` be a Noetherian scheme and `ℱ` a constructible sheaf of sets on `X_étale`. Then `ℱ`
embeds into a finite product `∏ᵢ fᵢ_* E̲ᵢ` with `fᵢ : Yᵢ ⟶ X` finite and `Eᵢ` a finite set
(Stacks 09Z6 (1)).

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleEtaleSetSheaf`: constructible sheaves of sets on
  Mathlib's small étale site, the transport of `AlgebraicGeometry.IsConstructibleSetSheaf` to the
  small étale site of Tag 021B, as `Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf` is for
  abelian sheaves.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_composeAndSheafify_free`: the free sheaf of
  `Λ`-modules on a constructible sheaf of sets is constructible.
* `CategoryTheory.Sheaf.mono_adjunction_free_unit`: a sheaf of sets embeds into the free sheaf of
  modules on it, over a nonzero ring.
* `Stacks.EtaleCohomology.exists_mono_pi_smallEtalePushforward_constantSheaf`: **Stacks 09Z6 (1)**,
  with the refinement of the last sentence of the tag.

## Implementation notes

The proof reduces to the case of modules, Stacks 09Z6 (3), over the finite ring
`Λ = ULift (ZMod 2)`. The free sheaf of `Λ`-modules `Λ[ℱ]` is constructible: in the model of
Tag 021B this is `AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_free`, and the
free module sheaf commutes with the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` between
the two models, both composites being left adjoint to the same functor. The unit `ℱ ⟶ Λ[ℱ]` is
injective because sheafification is locally injective and `ℱ` is separated. An embedding of
`Λ[ℱ]` into `⨁ᵢ fᵢ_* M̲ᵢ` with `Mᵢ` finite `Λ`-modules then gives the embedding of `ℱ` after
forgetting the module structure: forgetting commutes with direct images, carries the finite
biproduct to the product and the constant sheaf of modules to the constant sheaf of sets, and the
`Mᵢ` are finite sets because `Λ` is finite. The direct proof of the tag, through Stacks 09YV, 09Z4
and normalization, would repeat for sheaves of sets the whole of the module case.

## References

* [Stacks Project, Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v' u' u

attribute [-instance] Stacks.EtaleCohomology.TorsionModules.hasSheafify_smallEtaleTopology_moduleCat
attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace CategoryTheory.Sheaf

variable {C : Type u'} [Category.{v'} C] (J : GrothendieckTopology C) (Λ : Type (max u' v'))
  [Ring Λ] [Nontrivial Λ] [HasWeakSheafify J (ModuleCat.{max u' v'} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{max u' v'} Λ))]
  [J.PreservesSheafification (forget (ModuleCat.{max u' v'} Λ))]

/-- **A sheaf of sets embeds into the free sheaf of modules on it**, over a nonzero ring: the unit
of the free module sheaf adjunction is a monomorphism. Sectionwise the free module contains its
generators, and sheafification is locally injective, so the unit is locally injective; a map out of
a sheaf which is locally injective is injective. -/
@[sga "4 I 7.13" "more general"]
theorem mono_adjunction_free_unit (F : Sheaf J (Type (max u' v'))) :
    Mono ((Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F) := by
  have h₁ : Presheaf.IsLocallyInjective J
      (((ModuleCat.adj Λ).whiskerRight Cᵒᵖ).unit.app F.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun U x y h => by
      have h' : (Finsupp.single x 1 : F.obj.obj U →₀ Λ) = Finsupp.single y 1 := h
      exact Finsupp.single_left_injective one_ne_zero h'
  have h₂ := (Presheaf.isLocallyInjective_forget_iff J
    (toSheafify J (F.obj ⋙ ModuleCat.free Λ))).2 (Presheaf.isLocallyInjective_toSheafify' J _)
  have : Presheaf.IsLocallyInjective J ((Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F).hom := by
    rw [Sheaf.adjunction_unit_app_hom]
    exact Presheaf.isLocallyInjective_comp J
      (((ModuleCat.adj Λ).whiskerRight Cᵒᵖ).unit.app F.obj)
      (Functor.whiskerRight (toSheafify J (F.obj ⋙ ModuleCat.free Λ)) (forget (ModuleCat Λ)))
  exact Sheaf.mono_of_isLocallyInjective _

end CategoryTheory.Sheaf

namespace Stacks.EtaleCohomology

/-- **Constructible sheaves of sets** (Tag 03RW part (1)) on Mathlib's small étale site: the
transport of the sheaf to the small étale site of Tag 021B of the canonical big étale site
`AlgebraicGeometry.BigEtaleSite.containing X` is constructible in the sense of
`AlgebraicGeometry.IsConstructibleSetSheaf`, that is, on a finite partition of every affine open
into constructible locally closed subschemes its inverse images are finite locally constant. -/
@[sga "4 IX 2.3"]
abbrev IsConstructibleEtaleSetSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : Prop :=
  IsConstructibleSetSheaf (BigEtaleSite.containing X)
    ((BigEtaleSite.containing X).obj X (BigEtaleSite.contains_containing X))
    ((SmallEtale.sheafEquiv (BigEtaleSite.containing X) X (BigEtaleSite.contains_containing X)
      (Type (u + 1))).inverse.obj F)

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **The free sheaf of modules on a constructible sheaf of sets is constructible.** In the model
of Tag 021B this is `AlgebraicGeometry.isConstructibleModuleSheaf_composeAndSheafify_free`, and
the free module sheaf commutes with the equivalence of the two models of the small étale site:
both composites are left adjoint to restriction followed by forgetting the module structure. -/
theorem isConstructibleEtaleModule_composeAndSheafify_free {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (hF : IsConstructibleEtaleSetSheaf F) :
    IsConstructibleEtaleModule Λ
      ((Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.free Λ)).obj F) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, u + 1} B Λ f
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} Λ) := fun T V =>
    SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, u + 1} B Λ T V
  let K := SmallEtale.topology B X hX
  let E := SmallEtale.sheafEquiv B X hX (Type (u + 1))
  let EM := SmallEtale.sheafEquiv B X hX (ModuleCat.{u + 1} Λ)
  let adj₁ := E.toAdjunction.comp (Sheaf.adjunction X.smallEtaleTopology (ModuleCat.adj Λ))
  let adj₂ := (Sheaf.adjunction K (ModuleCat.adj Λ)).comp EM.toAdjunction
  let e : EM.inverse ⋙ sheafCompose K (forget (ModuleCat.{u + 1} Λ)) ≅
      sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ)) ⋙ E.inverse :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  let i := adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e)
  let G := (Sheaf.composeAndSheafify K (ModuleCat.free Λ)).obj (E.inverse.obj F)
  have hEG : IsConstructibleEtaleModule Λ (EM.functor.obj G) :=
    isConstructibleModuleSheaf_congr B Λ (B.obj X hX) (EM.unitIso.app G)
      (isConstructibleModuleSheaf_composeAndSheafify_free B (B.obj X hX) Λ _ hF)
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (((Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.free Λ)).mapIso
      (E.counitIso.app F)).symm ≪≫ i.app (E.inverse.obj F)).symm hEG

attribute [local instance 3000] Abelian.hasFiniteBiproducts

/-- **Stacks 09Z6 (1), with the refinement of its last sentence.** Let `X` be a Noetherian scheme
and `ℱ` a constructible sheaf of sets on `X_étale`. There is an injective map of sheaves
`ℱ ⟶ ∏ᵢ fᵢ_* E̲ᵢ` into a finite product, with `fᵢ : Yᵢ ⟶ X` finite (and of finite presentation)
and `Eᵢ` a finite set. Moreover each `Yᵢ` is irreducible and reduced and maps onto an irreducible
and reduced closed subscheme `Zᵢ` of `X` such that `Yᵢ ⟶ Zᵢ` is finite étale over a nonempty open
of `Zᵢ` (`AlgebraicGeometry.IsGenericallyFiniteEtaleOntoImage`).

The sheaves of sets take values in `Type (u + 1)`, the universe of
`AlgebraicGeometry.IsConstructibleSetSheaf`. -/
@[stacks 09Z6 "(1)", sga "4 IX 2.14" "(ii), special case"]
theorem exists_mono_pi_smallEtalePushforward_constantSheaf {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (hF : IsConstructibleEtaleSetSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ k, Y k ⟶ X) (_ : ∀ k, IsFinite (f k))
      (_ : ∀ k, FinitePresentation (f k)) (E : Fin n → Type (u + 1)) (_ : ∀ k, Finite (E k))
      (φ : F ⟶ ∏ᶜ fun k => (smallEtalePushforward (f k) (Type (u + 1))).obj
        ((constantSheaf (Y k).smallEtaleTopology (Type (u + 1))).obj (E k))),
      Mono φ ∧ ∀ k, IsGenericallyFiniteEtaleOntoImage (f k) := by
  let Λ := ULift.{u + 1} (ZMod 2)
  let J := X.smallEtaleTopology
  obtain ⟨n, Y, f, hf, hfp, M, hM, φ, hφ, -, hgen⟩ :=
    exists_mono_biproduct_etaleModuleDirectImage_constantSheaf_and_nsmul Λ
      ((Sheaf.composeAndSheafify J (ModuleCat.free Λ)).obj F)
      (isConstructibleEtaleModule_composeAndSheafify_free Λ F hF)
  have hpres : ∀ Z : Scheme.{u},
      Z.smallEtaleTopology.PreservesSheafification (forget (ModuleCat.{u + 1} Λ)) := fun Z =>
    Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat.{u, u + 1, 0} _ Λ
  let Fo : ∀ Z : Scheme.{u},
      EtaleModules.{u, u + 1} Λ Z ⥤ Sheaf Z.smallEtaleTopology (Type (u + 1)) :=
    fun Z => sheafCompose Z.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))
  let G : Fin n → EtaleModules.{u, u + 1} Λ X := fun k =>
    (etaleModuleDirectImage.{u, u + 1} Λ (f k)).obj
      ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M k))
  let e₁ : (Fo X).obj (⨁ G) ≅ ∏ᶜ fun k => (Fo X).obj (G k) :=
    (Fo X).mapIso (biproduct.isoProduct G) ≪≫ PreservesProduct.iso (Fo X) G
  let e₂ : ∀ k, (Fo X).obj (G k) ≅ (smallEtalePushforward (f k) (Type (u + 1))).obj
      ((constantSheaf (Y k).smallEtaleTopology (Type (u + 1))).obj (M k)) := fun k =>
    have := hpres (Y k)
    (Iso.refl _ : (Fo X).obj (G k) ≅ (smallEtalePushforward (f k) (Type (u + 1))).obj
        ((Fo (Y k)).obj ((constantSheaf (Y k).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (M k)))) ≪≫
      (smallEtalePushforward (f k) (Type (u + 1))).mapIso
        ((constantCommuteCompose (Y k).smallEtaleTopology
          (forget (ModuleCat.{u + 1} Λ))).app (M k))
  have hu : Mono ((Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F) :=
    have := hpres X
    Sheaf.mono_adjunction_free_unit J Λ F
  have hφ' : Mono ((Fo X).map φ) := Functor.map_mono _ _
  refine ⟨n, Y, f, hf, hfp, fun k => M k, fun k => ?_,
    (Sheaf.adjunction J (ModuleCat.adj Λ)).unit.app F ≫ (Fo X).map φ ≫ e₁.hom ≫
      (Pi.mapIso e₂).hom, mono_comp _ _, hgen⟩
  have := hM k
  exact Module.finite_of_finite Λ

end Stacks.EtaleCohomology

end
