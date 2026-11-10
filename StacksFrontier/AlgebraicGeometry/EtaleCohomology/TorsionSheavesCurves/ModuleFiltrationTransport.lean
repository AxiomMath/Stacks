module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NormalizationReduction
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# From sheaves of `F_ℓ`-vector spaces to abelian sheaves killed by `ℓ`

Tag 0A3R is stated for sheaves of `ZMod ℓ`-modules on a small étale site, while the eight
statements of Situation 0A52 are about abelian sheaves. This file supplies the forgetful
transport between the two and shows that it carries the conclusion of Tag 0A3R to the abelian
filtration `Stacks.EtaleCohomology.HasConstantFiltration` consumed by the last step of Lemma
03SD.

## Main definitions

* `Stacks.EtaleCohomology.forgetZMod`: the abelian sheaf underlying a sheaf of `ZMod ℓ`-modules.

## Main results

* `Stacks.EtaleCohomology.forgetZMod_shortExact`: the transport is exact.
* `Stacks.EtaleCohomology.forgetZModPullbackIso`: it commutes with inverse image.
* `Stacks.EtaleCohomology.forgetZModConstantIso`: it carries `Z/ℓZ` to the constant abelian sheaf.
* `Stacks.EtaleCohomology.hasConstantFiltration_forgetZMod_of_relSeries`: a filtration as in the
  conclusion of Tag 0A3R gives an abelian filtration with constant graded pieces.
* `Stacks.EtaleCohomology.exists_finiteEtale_hasConstantFiltration_of_primeToEll`: the
  conclusion of Tag 0A3R for a sheaf, read on its underlying abelian sheaf. This is the only
  lemma through which the dévissage of Theorem 03SC consumes Tag 0A3R.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Forget

variable (ℓ : ℕ) (X : Scheme.{u})

/-- `ZMod ℓ`-modules have all limits at the carrier universe `u + 1`. -/
instance hasLimitsOfSize_moduleCat_zmod :
    HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} (ZMod ℓ)) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}

/-- `ZMod ℓ`-modules have all colimits at the carrier universe `u + 1`. -/
instance hasColimitsOfSize_moduleCat_zmod :
    HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} (ZMod ℓ)) :=
  inferInstance

/-- Postcomposition with the forgetful functor of `ZMod ℓ`-modules carries sheaves to sheaves. -/
instance hasSheafCompose_forget₂_zmod :
    X.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _

/-- Postcomposition with the forgetful functor of `ZMod ℓ`-modules commutes with
sheafification. -/
instance preservesSheafification_forget₂_zmod :
    X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} _ _

/-- Presheaves of `ZMod ℓ`-modules on a small étale site admit sheafification. -/
instance hasSheafify_moduleCat_zmod :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} _ _

/-- **The abelian sheaf underlying a sheaf of `F_ℓ`-vector spaces** on the small étale site. -/
abbrev forgetZMod :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})

/-- The transport preserves finite limits, limits of sheaves being computed sectionwise. -/
instance preservesFiniteLimits_forgetZMod : PreservesFiniteLimits (forgetZMod ℓ X) := by
  refine ⟨fun I _ _ ↦ ?_⟩
  have : PreservesLimitsOfShape I (forgetZMod ℓ X ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfShape I
      (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- The transport preserves finite colimits: it commutes with sheafification and the forgetful
functor of modules preserves colimits. -/
instance preservesFiniteColimits_forgetZMod : PreservesFiniteColimits (forgetZMod ℓ X) :=
  ⟨fun _ _ _ ↦ Sheaf.preservesColimitsOfShape_sheafCompose _ _⟩

/-- The transport is additive. -/
instance additive_forgetZMod : (forgetZMod ℓ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The transport is exact.** -/
theorem forgetZMod_shortExact {S : ShortComplex (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} (ZMod ℓ)))} (hS : S.ShortExact) : (S.map (forgetZMod ℓ X)).ShortExact :=
  hS.map_of_exact _

/-- Every abelian sheaf underlying a sheaf of `ZMod ℓ`-modules is killed by `ℓ`. -/
theorem nsmul_id_forgetZMod_eq_zero (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    ℓ • 𝟙 ((forgetZMod ℓ X).obj G) = 0 := by
  have h : ℓ • 𝟙 G = 0 := by
    ext U x
    change (ℓ : ℕ) • x = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]
  simpa using congrArg (forgetZMod ℓ X).map h

/-- **The transport carries the constant sheaf `Z/ℓZ` to the constant abelian sheaf.** -/
def forgetZModConstantIso :
    (forgetZMod ℓ X).obj (constantZMod.{0} ℓ X) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod ℓ) X.smallEtaleTopology).app _

end Forget

section Pullback

variable (ℓ : ℕ) {S T : Scheme.{u}} (f : T ⟶ S)

/-- The forgetful functor of `ZMod ℓ`-modules preserves the colimits computing the presheaf
inverse image along base change. -/
instance preservesColimitsOfShape_costructuredArrow_forget₂_zmod (Y : T.Etaleᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange f).op Y)
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- **The transport commutes with inverse image**: the abelian sheaf underlying the inverse
image of a sheaf of `ZMod ℓ`-modules is the abelian inverse image of its underlying sheaf. Both
are sheaf pullbacks along the same functor of sites, read at two coefficient categories
(`CategoryTheory.Functor.sheafPullbackSheafComposeIso`), and the abelian sheaf pullback is
`Stacks.EtaleCohomology.etaleAbelianInverseImage` by uniqueness of left adjoints. -/
def forgetZModPullbackIso (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    (forgetZMod ℓ T).obj ((smallEtalePullbackZMod.{0} ℓ f).obj G) ≅
      (etaleAbelianInverseImage.{u, 0} f).obj ((forgetZMod ℓ S).obj G) :=
  ((smallEtaleBaseChange f).sheafPullbackSheafComposeIso (ModuleCat.{u + 1} (ZMod ℓ))
      S.smallEtaleTopology T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) G).symm ≪≫
    (Adjunction.leftAdjointUniq
      ((smallEtaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f)).app _

end Pullback

section Filtration

/-- `HasConstantFiltration` is invariant under isomorphism of the filtered sheaf. -/
theorem HasConstantFiltration.of_iso {S : Scheme.{u}} {E : AddCommGrpCat.{u + 1}} :
    ∀ {n : ℕ} {K K' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (_ : K ≅ K'),
      HasConstantFiltration E n K → HasConstantFiltration E n K'
  | 0, _, _, e, h => IsZero.of_iso h e.symm
  | _ + 1, _, _, e, ⟨T, hT, ⟨e₂⟩, h₁, h₃⟩ => ⟨T, hT, ⟨e₂ ≪≫ e⟩, h₁, h₃⟩

variable {ℓ : ℕ} {T : Scheme.{u}} {A : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))}

/-- One step of a filtration as in Tag 0A3R gives, after forgetting the module structure, a
short exact sequence of abelian sheaves whose quotient is the constant sheaf `Z/ℓZ`. -/
theorem exists_shortExact_forgetZMod_of_constantRankOneStep {P Q : Subobject A}
    (h : (P, Q) ∈ ConstantRankOneStep.{0} ℓ A) :
    ∃ Tc : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}), Tc.ShortExact ∧
      Nonempty (Tc.X₁ ≅ (forgetZMod ℓ T).obj (Subobject.underlying.obj P)) ∧
      Nonempty (Tc.X₂ ≅ (forgetZMod ℓ T).obj (Subobject.underlying.obj Q)) ∧
      Nonempty (Tc.X₃ ≅ (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) := by
  obtain ⟨hle, ⟨e⟩⟩ := h
  let Sc := ShortComplex.mk (P.ofLE Q hle) (cokernel.π (P.ofLE Q hle)) (cokernel.condition _)
  have hSc : Sc.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  exact ⟨Sc.map (forgetZMod ℓ T), forgetZMod_shortExact ℓ T hSc, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩,
    ⟨(forgetZMod ℓ T).mapIso e ≪≫ forgetZModConstantIso ℓ T⟩⟩

/-- **A filtration as in the conclusion of Tag 0A3R gives an abelian filtration with constant
graded pieces.** If `A` has a chain of subobjects from zero to the whole sheaf whose successive
quotients are `Z/ℓZ`, the underlying abelian sheaf of `A` is filtered by the constant sheaf
`ULift (ZMod ℓ)`, with as many steps as the chain. -/
theorem hasConstantFiltration_forgetZMod_of_relSeries
    (X : RelSeries (ConstantRankOneStep.{0} ℓ A))
    (hhead : IsZero (Subobject.underlying.obj X.head)) (hlast : IsIso X.last.arrow) :
    HasConstantFiltration (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) X.length
      ((forgetZMod ℓ T).obj A) := by
  have key : ∀ (i : ℕ) (hi : i < X.length + 1),
      HasConstantFiltration (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) i
        ((forgetZMod ℓ T).obj (Subobject.underlying.obj (X.toFun ⟨i, hi⟩))) := by
    intro i
    induction i with
    | zero => exact fun _ ↦ (forgetZMod ℓ T).map_isZero hhead
    | succ i ih =>
      intro hi
      obtain ⟨Tc, hTc, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
        exists_shortExact_forgetZMod_of_constantRankOneStep (X.step ⟨i, by omega⟩)
      exact ⟨Tc, hTc, ⟨e₂⟩, HasConstantFiltration.of_iso e₁.symm (ih (by omega)), ⟨e₃⟩⟩
  exact HasConstantFiltration.of_iso
    ((forgetZMod ℓ T).mapIso (asIso X.last.arrow)) (key X.length (by omega))

/-- **The conclusion of Tag 0A3R, read on abelian sheaves.** If a sheaf `G` of `F_ℓ`-vector
spaces on `S_étale` admits a finite étale `f : T ⟶ S` of degree `d` prime to `ℓ` for which
`f⁻¹G` is filtered with successive quotients `Z/ℓZ` (the conclusion of
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration`, verbatim), then the
abelian inverse image of the underlying abelian sheaf of `G` along the same `f` has a finite
filtration with graded pieces the constant sheaf `ULift (ZMod ℓ)`.

This is the single place where the conclusion of Tag 0A3R enters the dévissage of Theorem
03SC. -/
theorem exists_finiteEtale_hasConstantFiltration_of_primeToEll {S : Scheme.{u}}
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (h : ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj G)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow) :
    ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ n, HasConstantFiltration (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) n
        ((etaleAbelianInverseImage.{u, 0} f).obj ((forgetZMod ℓ S).obj G)) := by
  obtain ⟨T, f, d, hfin, het, hrk, hd, X, hhead, hlast⟩ := h
  exact ⟨T, f, d, hfin, het, hrk, hd, X.length, HasConstantFiltration.of_iso
    (forgetZModPullbackIso ℓ f G) (hasConstantFiltration_forgetZMod_of_relSeries X hhead hlast)⟩

end Filtration

end Stacks.EtaleCohomology

end
