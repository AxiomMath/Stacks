module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyElementaryFibration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# The top-degree trace of an elementary fibration: `R² f_!(f⁻¹ X) ≅ X`

Let `k` be an algebraically closed field, `N ≥ 1` invertible in `k`, and `f : U ⟶ S` an
elementary fibration (`AlgebraicGeometry.IsElementaryFibration`) over a quasi-compact and
quasi-separated `k`-scheme `S`: `f = f̄ ∘ j` with `f̄ : X̄ ⟶ S` smooth projective of relative
dimension one with geometrically irreducible fibres and `j` the complement of a closed `Z`
finite over `S`. Then for every compactification of `f` there is an isomorphism

`R² f_!(f⁻¹ X) ≅ X`,

natural in the sheaf `X` of `ℤ/N`-modules on `S_étale`
(`Stacks.EtaleCohomology.topLowerShriekTrace`,
`Stacks.EtaleCohomology.relativeTraceOfElementaryFibration`). At `X = ℤ/N` this is
`Stacks.EtaleCohomology.higherDirectImageTwoOfElementaryFibration`.

The isomorphism is the top-degree trace of the relative curve:

* by the independence of `Rf_!` of the compactification (Tag 0F7I) the compactification may be
  taken to be `j : U ⟶ X̄` over `f̄`, and then `R² f_! = R² f̄_* ∘ j_!`;
* the boundary is finite over `S`, so `R² f̄_*(j_! j⁻¹ f̄⁻¹X) ≅ R² f̄_*(f̄⁻¹X)`
  (`Stacks.EtaleCohomology.isIso_singleHomology_map_extensionByZero_counit`), naturally in `X`;
* the underlying abelian sheaf of `R² f̄_*(f̄⁻¹X)` is `H⁰(Rf̄_*(f̄⁻¹X[2]))`
  (`Stacks.EtaleCohomology.TopTrace.moduleTopSheafIso`), which is `X` by the top-degree trace of
  the Kummer class of the diagonal of `X̄ ×_S X̄`, descended along `f̄`
  (`Stacks.EtaleCohomology.TopTrace.topSheafIso`);
* the forgetful functor from sheaves of `ℤ/N`-modules to abelian sheaves is fully faithful.

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
`Rf_!` (`Stacks.EtaleCohomology.derivedLowerShriek`) is stated.

## Main definitions

* `Stacks.EtaleCohomology.topLowerShriekTraceOfCompactification`: the isomorphism, from the data of
  the elementary fibration and a primitive `N`-th root of unity.
* `Stacks.EtaleCohomology.topLowerShriekTrace`: the isomorphism for an elementary fibration.
* `Stacks.EtaleCohomology.RelativeTraceOfElementaryFibration`: the statement that
  `X ↦ R² f_!(f⁻¹ X)` is isomorphic to the identity for every elementary fibration and every
  compactification of it.

## Main results

* `Stacks.EtaleCohomology.nonempty_topLowerShriekTrace`: `R² f_!(f⁻¹ G) ≅ G`, naturally in `G`,
  for an elementary fibration `f`.
* `Stacks.EtaleCohomology.relativeTraceOfElementaryFibration`: the relative trace exists over an
  algebraically closed field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

/-! ### The construction, from the data of the fibration -/

section Construction

variable {k : Type u} [Field k] (N : ℕ) [NeZero N] (hN : IsUnit (N : k))
  {U S Xbar Z : Scheme.{u}} (q : S ⟶ Spec (.of k)) (f : U ⟶ S) (j : U ⟶ Xbar)
  [IsOpenImmersion j] (fbar : Xbar ⟶ S) (hjf : j ≫ fbar = f) [IsProper fbar]
  [SmoothOfRelativeDimension 1 fbar] [GeometricallyIrreducible fbar] (i : Z ⟶ Xbar)
  [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ) [IsIntegralHom (i ≫ fbar)]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] (jf : CompactificationOf (Over.mk f)) {ζ : k} (hζ : IsPrimitiveRoot ζ N)

/-- The compactification `j : U ⟶ X̄` of `f` over `f̄`. -/
def compactificationOfFactorization : CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (Y := Over.mk fbar) (Over.homMk (U := Over.mk f) j hjf),
    ⟨inferInstanceAs (IsOpenImmersion j), inferInstanceAs (IsProper fbar)⟩⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f] in
/-- The inverse image `f⁻¹ G` placed in degree zero is a torsion object. -/
theorem isTorsionPlus_single_inverseImage (G : EtaleModules.{u, 0} (ZMod N) S) :
    isTorsionPlus.{u, 0} (ZMod N) U ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) f).obj G)) :=
  fun _ => isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (Nat.pos_of_ne_zero (NeZero.ne N))
    (ZMod.natCast_self N) _

/-- `f⁻¹(-)[0]`, as a functor to the torsion objects of `D⁺`. -/
def inverseImageSingleTorsion :
    EtaleModules.{u, 0} (ZMod N) S ⥤ (isTorsionPlus.{u, 0} (ZMod N) U).FullSubcategory :=
  ObjectProperty.lift _ (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙
    DerivedCategory.Plus.singleFunctor _ 0) (isTorsionPlus_single_inverseImage N f)

/-- `singlePlus ⋙ Q ≅ Plus.single` inside `R² f_!(f⁻¹ -)`. -/
def lowerShriekHomologyTwoIso₁ :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ lowerShriekHomology (ZMod N) f jf 2 ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ 2) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
    (Functor.isoWhiskerRight
      (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} (ZMod N) U))
      (derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ 2))

/-- The independence of the compactification (Tag 0F7I) inside `R² f_!(f⁻¹ -)`. -/
def lowerShriekHomologyTwoIso₂ :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ 2) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙
          DerivedCategory.Plus.homologyFunctor _ 2) :=
  Functor.isoWhiskerLeft (inverseImageSingleTorsion N f)
    (Functor.isoWhiskerRight (derivedLowerShriekCompactificationIso f jf
      (compactificationOfFactorization f j fbar hjf) (ZMod N))
      (DerivedCategory.Plus.homologyFunctor _ 2))

/-- `Rf_! = Rf̄_* ∘ j_!` on a sheaf placed in degree zero, for the compactification `j`. -/
def lowerShriekHomologyTwoIso₃ :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f (compactificationOfFactorization f j fbar hjf) (ZMod N) ⋙
          DerivedCategory.Plus.homologyFunctor _ 2) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2) :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod N) U
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) f)
    (Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) 0).symm
        (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
          DerivedCategory.Plus.homologyFunctor _ 2) ≪≫
      Functor.isoWhiskerLeft (etaleModuleExtensionByZero.{u, 0} (ZMod N) j)
        (Functor.isoWhiskerRight
          (StacksDraft.DerivedSectionsComparison.singlePlusQIso (EtaleModules.{u, 0} (ZMod N) Xbar))
          (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar ⋙
            DerivedCategory.Plus.homologyFunctor _ 2)).symm)

/-- `f⁻¹ = j⁻¹ f̄⁻¹`, and `j⁻¹` is restriction. -/
def lowerShriekHomologyTwoIso₄ :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙ (etaleModuleRestriction.{u, 0} (ZMod N) j ⋙
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
          singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2)) :=
  Functor.isoWhiskerRight (eqToIso (congrArg (etaleModuleInverseImage.{u, 0} (ZMod N)) hjf.symm) ≪≫
      etaleModuleInverseImageCompIso.{u, 0} (ZMod N) j fbar ≪≫
      Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
        (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j))
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2) ≪≫
    Functor.associator _ _ _

include i hij in
/-- The boundary: `R² f̄_*(j_! j⁻¹ M) ≅ R² f̄_* M`, the complement of `j` being finite over `S`. -/
def lowerShriekHomologyTwoIso₅ :
    etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙ (etaleModuleRestriction.{u, 0} (ZMod N) j ⋙
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j ⋙
          singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2)) ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2 :=
  haveI : IsIso (Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
      (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit
        (singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun _ => isIso_singleHomology_map_extensionByZero_counit (ZMod N) i j hij fbar _ 2 le_rfl
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
      (Functor.associator _ _ _).symm ≪≫
    asIso (Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar)
      (Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) j).counit
        (singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2))) ≪≫
    Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} (ZMod N) fbar) (Functor.leftUnitor _)

include i hij in
/-- **`R² f_!(f⁻¹ G) ≅ R² f̄_*(f̄⁻¹ G)`**, naturally in `G`: independence of the compactification
(Tag 0F7I), `Rj_!` on a sheaf, `f⁻¹ = j⁻¹ f̄⁻¹`, and the boundary finite over `S`. -/
def lowerShriekHomologyTwoIso :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ lowerShriekHomology (ZMod N) f jf 2 ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) fbar ⋙
        singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod N) fbar) 2 :=
  lowerShriekHomologyTwoIso₁ N (f := f) (jf := jf) ≪≫
    lowerShriekHomologyTwoIso₂ N (f := f) (j := j) (fbar := fbar) (hjf := hjf) (jf := jf) ≪≫
    lowerShriekHomologyTwoIso₃ N (f := f) (j := j) (fbar := fbar) (hjf := hjf) ≪≫
    lowerShriekHomologyTwoIso₄ N (f := f) (j := j) (fbar := fbar) (hjf := hjf) ≪≫
    lowerShriekHomologyTwoIso₅ N (j := j) (fbar := fbar) (i := i) (hij := hij)

include hN q i hij hζ in
/-- **The top-degree trace of an elementary fibration**, from the data of the fibration and a
primitive `N`-th root of unity of `k`: `R² f_!(f⁻¹ G) ≅ G`, naturally in the sheaf `G` of
`ℤ/N`-modules on `S`. -/
def topLowerShriekTraceOfCompactification :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ lowerShriekHomology (ZMod N) f jf 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S) :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse
  have hX : IsUnit ((N : ℕ) : Γ(Xbar, ⊤)) := isUnit_natCast_sections k (fbar ≫ q) hN
  have hY : IsUnit ((N : ℕ) : Γ(pullback fbar fbar, ⊤)) :=
    isUnit_natCast_sections k (pullback.fst fbar fbar ≫ fbar ≫ q) hN
  ((Stacks.ArtinSchreier.etaleModuleForgetZModFullyFaithful S N).whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight
        (lowerShriekHomologyTwoIso N (f := f) (j := j) (fbar := fbar) (hjf := hjf) (i := i)
          (hij := hij) (jf := jf))
        (etaleModuleUnderlyingAbelian S (ZMod N)) ≪≫
      Functor.associator _ _ _ ≪≫
      TopTrace.moduleTopSheafIso fbar ≪≫
      (TopTrace.topSheafIso fbar hX hY (pullback.fst fbar fbar ≫ fbar ≫ q) hζ).symm ≪≫
      (Functor.leftUnitor _).symm)

end Construction

/-! ### For an elementary fibration -/

section Fibration

variable {k : Type u} [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]

include k in
/-- **`R² f_!(f⁻¹ G) ≅ G` for an elementary fibration**, naturally in the sheaf `G`. -/
theorem nonempty_topLowerShriekTrace (hN : IsUnit (N : k)) {U S : Scheme.{u}}
    (q : S ⟶ Spec (.of k)) (f : U ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [QuasiCompact f] (hf : IsElementaryFibration f) (jf : CompactificationOf (Over.mk f)) :
    Nonempty (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ lowerShriekHomology (ZMod N) f jf 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S)) := by
  obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, hgi, hi, -, hrange, hfin, -, -⟩ :=
    hf.exists_compactification
  have := hj
  have := hsm
  have := hgi
  have := hi
  have := hfin
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  have : IsSeparated f := by rw [← hjf]; infer_instance
  have : LocallyOfFiniteType f := by rw [← hjf]; infer_instance
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k N
  exact ⟨topLowerShriekTraceOfCompactification N hN (q := q) (f := f) (j := j) (fbar := fbar)
    (hjf := hjf) (i := i) (hij := by rw [hrange, compl_compl]) (jf := jf) (hζ := hζ)⟩

/-- **The top-degree trace of an elementary fibration** `f : U ⟶ S` over a quasi-compact and
quasi-separated `k`-scheme, `k` algebraically closed and `N` invertible in `k`:
`R² f_!(f⁻¹ G) ≅ G`, naturally in the sheaf `G` of `ℤ/N`-modules on `S`, for every
compactification of `f`. -/
def topLowerShriekTrace (hN : IsUnit (N : k)) {U S : Scheme.{u}} (q : S ⟶ Spec (.of k))
    (f : U ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact f]
    (hf : IsElementaryFibration f) (jf : CompactificationOf (Over.mk f)) :
    etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ lowerShriekHomology (ZMod N) f jf 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod N) S) :=
  (nonempty_topLowerShriekTrace N hN q f hf jf).some

end Fibration

/-! ### The relative trace of an elementary fibration -/

variable (k : Type u) [Field k] (N : ℕ) [NeZero N]

/-- **The relative trace of an elementary fibration**: for `N` invertible in `k` and an elementary
fibration `f : U → S` over `S` affine and smooth over `k`, for every compactification of `f`,
`X ↦ R²f_!(f⁻¹X)` is isomorphic to the identity, naturally in the sheaf `X` of `ℤ/N`-modules. -/
def RelativeTraceOfElementaryFibration (k : Type u) [Field k] (N : ℕ) [NeZero N] : Prop :=
  IsUnit (N : k) → ∀ (U S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U ⟶ S) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S],
    IsElementaryFibration f → ∀ jf : CompactificationOf (Over.mk f),
    Nonempty (etaleModuleInverseImage.{u, 0} (ZMod N) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
      derivedLowerShriek.{u, 0} f jf (ZMod N) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
        𝟭 (EtaleModules.{u, 0} (ZMod N) S))

/-- **The relative trace of an elementary fibration exists** over an algebraically closed
field: `R²f_!(f⁻¹X) ≅ X`, naturally in the sheaf `X` of `ℤ/N`-modules. -/
theorem relativeTraceOfElementaryFibration [IsAlgClosed k] :
    RelativeTraceOfElementaryFibration k N := by
  intro hN U S q f e _ _ hf jf
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian S := ⟨⟩
  have : QuasiCompact f := by
    obtain ⟨Xbar, Z, j, fbar, i, hj, hjf, hsm, hproj, -, -, -, -, -, -, -⟩ :=
      hf.exists_compactification
    have := hj
    have := hsm
    have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
    have : CompactSpace Xbar := ⟨by
      simpa using QuasiCompact.isCompact_preimage (f := fbar) Set.univ isOpen_univ isCompact_univ⟩
    have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian fbar
    have : IsNoetherian Xbar := ⟨⟩
    have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
    rw [← hjf]
    infer_instance
  exact ⟨(lowerShriekHomologyTwoIso₁ N (f := f) (jf := jf)).symm ≪≫
    topLowerShriekTrace N hN q f hf jf⟩

end Stacks.EtaleCohomology
