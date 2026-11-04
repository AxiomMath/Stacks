module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.DerivedTensorArbitraryScheme
public import StacksFrontier.Homology.KFlat.BifunctorOneSided
public import StacksFrontier.RingTheory.Flat.Prod
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on `D(X_étale, Λ)`, and Stacks 0961 for it

Let `X` be an object of a big étale site and `Λ` a commutative ring. This file constructs the
derived tensor product

`- ⊗^L_Λ - : D(X_étale, Λ) ⥤ D(X_étale, Λ) ⥤ D(X_étale, Λ)`

on the unbounded derived category of sheaves of `Λ`-modules on the small étale site of `X`, as
the derived functor of the tensor product of sheaves of `Λ`-modules computed on K-flat
resolutions (Stacks 06YU), and proves Stacks Tag 0961 for it: for an arbitrary scheme `X`, a
Noetherian ring `Λ` and `K, L ∈ D_c^-(X_étale, Λ)`, the derived tensor product `K ⊗^L_Λ L` is in
`D_c^-(X_étale, Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleSheafDerivedTensor` — **the derived tensor product
  `⊗^L_Λ` on `D(X_étale, Λ)`**: `CochainComplex.KFlatBifunctor.derivedBifunctor` of the tensor
  product `AlgebraicGeometry.SmallEtale.moduleSheafMonoidal` of sheaves of `Λ`-modules, the
  descent of `Tot(- ⊗_Λ -)` along the localizations of the K-flat complexes at the
  quasi-isomorphisms.

## Main results

* `Stacks.EtaleCohomology.exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf` — **Stacks 06YS for
  sheaves of `Λ`-modules on the small étale site**: every complex receives a quasi-isomorphism
  from a complex which is K-flat on either side.
* `Stacks.EtaleCohomology.isDerivedTensorOnFlatComplexes_etaleModuleSheafDerivedTensor` — the
  derived tensor product is computed by the total tensor complex as soon as the right factor is
  a bounded above complex of flat sheaves: that is
  `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes`, now a theorem about
  `etaleModuleSheafDerivedTensor` rather than a hypothesis on an unnamed bifunctor.
* `Stacks.EtaleCohomology.minus_and_isConstructible_etaleModuleSheafDerivedTensor` —
  **Stacks 0961**.

## The construction

The derived tensor product is the abstract one of `CochainComplex.KFlatBifunctor`, instantiated
at `curriedTensor` of the sheaf category. Its only input is a supply of K-flat resolutions, on
each side, and that is Stacks 06YS, proved here by the source's argument (Stacks 077J, 06XX,
06YR): the ladder of resolutions of the canonical truncations `τ_{≤ n} G`
(`CochainComplex.exists_sequence_quasiIso_truncLE`), built from the class of sheaves whose
étale stalks are flat — it contains zero, is closed under direct sums, and every sheaf is a
quotient of a member of it by `AlgebraicGeometry.exists_epi_flat_etaleModuleStalk` (the
generators `j_{U!}\underline{Λ}` of Stacks 093B (2)) — has bounded above stages with flat
étale stalks, which are K-flat on either side by Stacks 06YQ
(`Stacks.EtaleCohomology.kFlat_of_flat_etaleModuleStalk`); K-flatness passes to the sequential
colimit (`CochainComplex.KFlatBifunctor.kFlat_of_isColimit`), and the colimit maps
quasi-isomorphically to `G`
(`StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE`).

## Stacks 0961

Flatness of a sheaf of `Λ`-modules is, in `IsDerivedTensorOnFlatComplexes`, flatness over the
constant coefficient ring sheaf; by Stacks 05VB its étale stalks are then flat `Λ`-modules
(`AlgebraicGeometry.etaleModuleStalk_flat_of_isFlat_terms`), so a bounded above complex of flat
sheaves is K-flat by Stacks 06YQ and computes the derived tensor product as its total tensor
complex (`CochainComplex.KFlatBifunctor.comparisonRight`). With that, the arbitrary-scheme argument
of `Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_arbitraryScheme` — the
bounded above flat representatives of Stacks 05T7, the quasi-compact quasi-separated case of
Stacks 0960 and 095I, and Zariski descent for constructibility, Stacks 095F — applies to the
derived tensor product itself.

## References

* [Stacks Project, Tag 0961](https://stacks.math.columbia.edu/tag/0961)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.SmallEtale.moduleSheafMonoidal
  AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

attribute [local instance] hasLimitsOfSize_moduleCat in
/-- The étale stalk of a direct sum of two sheaves of `Λ`-modules with flat stalk at a
geometric point is flat there. -/
private theorem flat_etaleModuleStalk_biprod (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type (max (u + 1) w)) [CommRing Λ] {s : GeometricPoint X.obj}
    (Y Z : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hY : Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w}
      B X Λ s).obj Y))
    (hZ : Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w}
      B X Λ s).obj Z)) :
    Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w}
      B X Λ s).obj (Y ⊞ Z)) := by
  set F := etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s
  have : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    preservesColimitsOfShape_etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w, 0, 0}
      B X Λ s _
  have : PreservesBinaryBiproduct Y Z F := preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  have : Module.Flat Λ (F.obj Y × F.obj Z) := Module.Flat.prod
  exact Module.Flat.of_linearEquiv
    ((F.mapBiprod Y Z ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv)

/-! ### K-flat resolutions -/

section Resolution

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (max (u + 1) w)) [CommRing Λ]
  [(curriedTensor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]
  [∀ K : HomologicalComplex₂ (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]

attribute [local instance] ab5OfSize_moduleCat hasLimitsOfSize_moduleCat additive_tensorRight
  monoidalClosed_moduleSheaf hasExactColimitsOfShape_nat_moduleSheaf braided_moduleSheaf
  additive_curriedTensor_flip

/-- **Stacks 06YS for sheaves of `Λ`-modules on the small étale site.** Every complex of
sheaves of `Λ`-modules receives a quasi-isomorphism from a complex which is K-flat for the
tensor product on either side.

The resolution is the colimit of the ladder of Stacks 06XX resolving the canonical truncations
`τ_{≤ n} G` by bounded above complexes of sheaves with flat étale stalks; each stage is K-flat
on either side by Stacks 06YQ, and K-flatness passes to the sequential colimit, Stacks 06YR,
because tensoring is a left adjoint and sequential colimits are exact. -/
theorem exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf
    (G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ) :
    ∃ (P : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)) ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Sheaf
        (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))) P ∧
      CochainComplex.KFlatBifunctor.KFlatLeft (curriedTensor (Sheaf
        (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))) P ∧
      QuasiIso f := by
  classical
  set P : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) :=
    fun F => ∀ s : GeometricPoint X.obj, Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj F)
  have hzero : P.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))
    refine ⟨⟨Z, hZ, fun s => ?_⟩⟩
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).map_isZero hZ)
    infer_instance
  have hsum : ∀ Y Z : Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ), P Y → P Z → P (Y ⊞ Z) :=
    fun Y Z hY hZ s => flat_etaleModuleStalk_biprod B X Λ Y Z (hY s) (hZ s)
  obtain ⟨Q, q, g, hq, -, hle, hflat, -, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum
      (exists_epi_flat_etaleModuleStalk.{u, max (u + 1) w} B X Λ) G
  let D := Functor.ofSequence g
  let c := colimit.cocone D
  have hc : IsColimit c := colimit.isColimit D
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n ↦ q n ≫ G.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  let α : c.pt ⟶ G := hc.desc s
  have hα : ∀ n : ℕ, c.ι.app n ≫ α = q n ≫ G.ιTruncLE (n : ℤ) := fun n ↦ hc.fac s n
  have hL : ∀ Y : Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ), PreservesColimitsOfShape ℕ (tensorLeft Y) := fun Y =>
    (ihom.adjunction Y).leftAdjoint_preservesColimits.preservesColimitsOfShape
  refine ⟨c.pt, α, ?_, ?_,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE
      q hq hc α hα⟩
  · refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ c hc hL
      (acyclic_of_isColimit_nat B X Λ) (fun n => ?_)
    have := hle n
    exact kFlat_of_flat_etaleModuleStalk B X Λ (Q n) n (hflat n)
  · refine (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ c.pt).2
      (CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ c hc (fun Y => ?_)
        (acyclic_of_isColimit_nat B X Λ) (fun n => ?_))
    · have := hL Y
      exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Y)
    · have := hle n
      exact (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ _).1
        (kFlatLeft_of_flat_etaleModuleStalk B X Λ (Q n) n (hflat n))

/-- **The K-flat resolutions of Stacks 06YS on the small étale site, as an instance**: the
K-flat half of `Stacks.EtaleCohomology.exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf`, in the
form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` takes, so that
`D(X_étale, Λ)` is the localization of the K-flat complexes at the quasi-isomorphisms. -/
instance etaleModuleSheaf_kFlatLocalizer_hasLeftResolutions :
    (CochainComplex.KFlatBifunctor.kFlatLocalizer (curriedTensor (Sheaf
        (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)))).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizer_hasLeftResolutions _ fun G => by
    obtain ⟨P, f, hP, -, hf⟩ := exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf B X Λ G
    exact ⟨P, f, hP, hf⟩

/-- **The left K-flat resolutions of Stacks 06YS on the small étale site, as an instance**: the
left K-flat half of `Stacks.EtaleCohomology.exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf`,
in the form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions` takes, so that
`D(X_étale, Λ)` is the localization of the left K-flat complexes at the quasi-isomorphisms. -/
instance etaleModuleSheaf_kFlatLocalizerLeft_hasLeftResolutions :
    (CochainComplex.KFlatBifunctor.kFlatLocalizerLeft (curriedTensor (Sheaf
        (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)))).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizerLeft_hasLeftResolutions _ fun G => by
    obtain ⟨P, f, -, hP, hf⟩ := exists_kFlat_kFlatLeft_quasiIso_etaleModuleSheaf B X Λ G
    exact ⟨P, f, hP, hf⟩

/-! ### The derived tensor product -/

/-- **The derived tensor product `- ⊗^L_Λ -` on `D(X_étale, Λ)`**, Stacks 06YU for sheaves of
`Λ`-modules on the small étale site: the derived functor of the tensor product of sheaves of
`Λ`-modules, obtained by descending `Tot(- ⊗_Λ -)` along the localizations of the (left)
K-flat complexes at the quasi-isomorphisms. On K-flat representatives it is the total tensor
complex, `CochainComplex.KFlatBifunctor.comparisonRight`. -/
abbrev etaleModuleSheafDerivedTensor :
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) :=
  CochainComplex.KFlatBifunctor.derivedBifunctor (curriedTensor (Sheaf
    (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))

/-- **A bounded above complex of flat sheaves computes the derived tensor product.** The value
of `K ⊗^L_Λ L` at the classes of two complexes is the class of their total tensor complex as
soon as the right factor is bounded above with terms flat over the constant coefficient ring
sheaf: those terms have flat étale stalks by Stacks 05VB, so the complex is K-flat by
Stacks 06YQ, and a K-flat right factor computes the derived bifunctor. -/
theorem isDerivedTensorOnFlatComplexes_etaleModuleSheafDerivedTensor
    [∀ (S S' : B.Scheme) (f : S' ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint] :
    IsDerivedTensorOnFlatComplexes.{u, w} B X Λ (etaleModuleSheafDerivedTensor B X Λ) := by
  intro P G q _ hflat
  exact ⟨CochainComplex.KFlatBifunctor.comparisonRight _ P G
    (kFlat_of_flat_etaleModuleStalk B X Λ G q
      (etaleModuleStalk_flat_of_isFlat_terms B X Λ G hflat))⟩

end Resolution

/-! ### Stacks 0961 -/

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S S' : B.Scheme) (f : S' ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint]
  [∀ (S : B.Scheme) (V : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]
  [∀ S : B.Scheme, (curriedTensor
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ (S : B.Scheme)
      (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)),
    ((curriedTensor (Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]
  [∀ (S : B.Scheme) (K : HomologicalComplex₂
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)), K.HasTotal (ComplexShape.up ℤ)]

/-- **Stacks 0961.** Let `X` be a scheme, `Λ` a Noetherian ring and `K, L ∈ D_c^-(X_étale, Λ)`.
Then `K ⊗_Λ^L L` is in `D_c^-(X_étale, Λ)`: it is bounded above, and all of its cohomology
sheaves are constructible.

The derived tensor product is `Stacks.EtaleCohomology.etaleModuleSheafDerivedTensor`, the
derived functor of the tensor product of sheaves of `Λ`-modules on K-flat resolutions, and
nothing is assumed of it or of `X`. That it is computed by the total tensor complex on a bounded
above complex of flat sheaves is proved,
`Stacks.EtaleCohomology.isDerivedTensorOnFlatComplexes_etaleModuleSheafDerivedTensor`, and the
rest is the arbitrary-scheme argument of
`Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_arbitraryScheme`. -/
@[stacks 0961 "for the derived tensor product of sheaves of Lambda-modules on the small etale \
  site of an arbitrary scheme, built on K-flat resolutions (Stacks 06YS, 06YU) and shown to be \
  computed by total tensor complexes on bounded above complexes of flat sheaves (Stacks 06YQ)"]
theorem minus_and_isConstructible_etaleModuleSheafDerivedTensor (X : B.Scheme)
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B X Λ K.obj) (hL : IsConstructible B X Λ L.obj) :
    (DerivedCategory.TStructure.t (C := Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))).minus
        (((etaleModuleSheafDerivedTensor B X Λ).obj K.obj).obj L.obj) ∧
      IsConstructible B X Λ (((etaleModuleSheafDerivedTensor B X Λ).obj K.obj).obj L.obj) :=
  minus_and_isConstructible_derivedTensor_of_arbitraryScheme B Λ X _
    (isDerivedTensorOnFlatComplexes_etaleModuleSheafDerivedTensor B X Λ) K L hK hL

end Stacks.EtaleCohomology

end
