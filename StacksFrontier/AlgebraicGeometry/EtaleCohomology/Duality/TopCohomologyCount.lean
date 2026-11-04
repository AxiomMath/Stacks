module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyFibration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityInduction
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.ElementaryFibration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothStratumOfClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# The top compactly supported cohomology of a smooth variety, through an elementary fibration

Let `k` be a separably closed field, `N > 0` and `Λ = ℤ/N`. Let `W` be smooth irreducible of
relative dimension `e + 1` over `k` with a compactification `j : W → X̄`, and let `U ⊆ W` be a
nonempty open which is an elementary fibration `f : U → S` over `S` smooth irreducible affine of
relative dimension `e`. If `R²f_! Λ ≅ Λ_S`, then

`H^{2e+2}_c(W) ≅ H^{2e+2}_c(U) ≅ H^{2e}_c(S)`,

the first isomorphism because the complement of `U` has dimension at most `e`
(`Stacks.EtaleCohomology.bijective_ext_extensionByZero_counit_of_closed`), the second by the
Leray isomorphism and the corner of its spectral sequence
(`Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_of_higherDirectImage_two_iso`), for the
compactification of `S` given by the closure of `S` in any compactification, which has dimension
`e`.

## Main results

* `AlgebraicGeometry.isProper_of_smoothOfRelativeDimension_zero`.
* `Stacks.EtaleCohomology.exists_ext_top_addEquiv_of_isElementaryFibration`.
* `Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod`: `H^{2e}_c(W, ℤ/N) ≅ ℤ/N`, given dense
  elementary fibrations and `R²f_! ℤ/N ≅ ℤ/N` for them.
* `Stacks.EtaleCohomology.natCard_ext_unitSheaf_top_pow`: `H^{2d}(Y, ℤ/ℓ^{m+1}) ≅ ℤ/ℓ^{m+1}` for
  `Y` connected smooth proper.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **A smooth irreducible variety of relative dimension zero with a compactification is
proper**: its closure in the compactification is irreducible of dimension zero, so a single
point, and the open immersion into it is an isomorphism. -/
theorem isProper_of_smoothOfRelativeDimension_zero {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 0 p] [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk p)) : IsProper p := by
  let jS := (jc.restrictOpen (𝟙 W)).restrictClosed (𝟙 W)
  have : SmoothOfRelativeDimension 0 (𝟙 W ≫ 𝟙 W ≫ p) := by
    simp only [Category.id_comp]
    infer_instance
  have hdim := Stacks.EtaleCohomology.topologicalKrullDim_restrictClosed_space_le p jc (𝟙 W)
    (𝟙 W) 0
  let g := (jc.restrictOpen (𝟙 W)).closedImmersion (𝟙 W)
  obtain ⟨x⟩ := (‹IrreducibleSpace W›).toNonempty
  have : IrreducibleSpace jS.space := by
    rw [irreducibleSpace_def]
    have h := ((IrreducibleSpace.isIrreducible_univ W).image g.toImage.base
      g.toImage.base.hom.continuous.continuousOn).closure
    rwa [Set.image_univ, g.toImage.denseRange.closure_range] at h
  have := StacksTag09NX.subsingleton_of_topologicalKrullDim_le_zero jS.space (by exact hdim)
  have : Epi jS.immersion.base :=
    (TopCat.epi_iff_surjective _).2 fun y => ⟨x, Subsingleton.elim _ _⟩
  have : IsIso jS.immersion := IsOpenImmersion.isIso _
  have h : jS.immersion ≫ jS.toBase = p := by
    rw [CompactificationOf.immersion_toBase]
    simp
  rw [← h]
  infer_instance

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] (N : ℕ) [NeZero N]

/-- **`H⁰(Y, ℤ/N) ≅ ℤ/N` on a connected `Y`**, read as `Ext⁰(ℤ/N_Y, ℤ/N_Y)`: maps out of the
constant sheaf are global sections, which are the locally constant functions, hence constant. -/
def extZeroUnitSheafAddEquivOfConnectedSpace (Y : Scheme.{u}) [ConnectedSpace Y] :
    Ext (unitSheaf (X := Y) N) (unitSheaf (X := Y) N) 0 ≃+ ZMod N :=
  Ext.addEquiv₀.trans <|
    ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
      (etaleSiteTerminalIsTerminal Y)).homAddEquiv _ _).trans <|
    (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} (ZMod N) _).trans <|
    (((sheafToPresheaf _ _).mapIso (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0}
      (ZMod N) Y (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))))).app
        (Opposite.op (etaleSiteTerminal Y))).toLinearEquiv.toAddEquiv.trans <|
    (AddEquiv.ofBijective (LocallyConstant.constAddMonoidHom (X := Y))
      ⟨fun a b h => by
        obtain ⟨y⟩ := (‹ConnectedSpace Y›).toNonempty
        simpa using congrArg (fun φ : LocallyConstant Y _ => φ y) h,
       fun φ => by
        obtain ⟨y⟩ := (‹ConnectedSpace Y›).toNonempty
        refine ⟨φ y, LocallyConstant.ext fun z => ?_⟩
        exact (φ.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ
          (Set.mem_univ z) (Set.mem_univ y)).symm⟩).symm.trans AddEquiv.ulift

/-- **`Hⁱ_c` does not depend on the compactification**, read in `Ext`: for two compactifications
`j₁`, `j₂` of `p : W → Spec k` and a sheaf `K` of `ℤ/N`-modules,
`Ext^i_{X̄₁}(Λ, (j₁)_! K) ≅ Ext^i_{X̄₂}(Λ, (j₂)_! K)` (Tag 0F7I and the computation of `Hⁱ_c` as
`Ext` on the compactification). -/
theorem nonempty_ext_addEquiv_of_compactifications {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (j₁ j₂ : CompactificationOf (Over.mk p)) (K : EtaleModules.{u, 0} (ZMod N) W) (i : ℕ) :
    Nonempty (Ext (unitSheaf (X := j₁.space) N)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j₁.immersion).obj K) i ≃+
      Ext (unitSheaf (X := j₂.space) N)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j₂.immersion).obj K) i) := by
  have hK : isTorsionPlus.{u, 0} (ZMod N) W ((DerivedCategory.Plus.singleFunctor _ 0).obj K) :=
    fun _ => isTorsionEtaleModule_of_natCast_eq_zero (ZMod N) N (NeZero.pos N)
      (ZMod.natCast_self N) _
  let e := (derivedLowerShriekCompactificationIso p j₁ j₂ (ZMod N)).app ⟨_, hK⟩
  let e' := (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).mapIso
    ((DerivedCategory.Plus.homologyFunctor _ (i : ℤ)).mapIso
      ((etaleModuleDerivedGlobalSections.{u, 0} (ZMod N) (Spec (.of k))).mapIso e))
  exact ⟨((compactlySupportedCohomologyGroupSingleIsoExt (ZMod N) k p j₁ K i).symm ≪≫ e' ≪≫
    compactlySupportedCohomologyGroupSingleIsoExt (ZMod N) k p j₂ K i).addCommGroupIsoToAddEquiv⟩

/-- Postcomposition with an isomorphism `f : B ⟶ C` is an additive equivalence on `Ext`. -/
private def extPostcompAddEquiv {X : Scheme.{u}} {A B C : EtaleModules.{u, 0} (ZMod N) X}
    (f : B ⟶ C) [IsIso f] (n : ℕ) : Ext A B n ≃+ Ext A C n :=
  AddEquiv.ofBijective ((Ext.mk₀ f).postcomp A (add_zero n))
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso f n)

/-- `Ext^n(ℤ/N, (𝟙 W)_! ℤ/N) ≅ Ext^n(ℤ/N, ℤ/N)`, as extension by zero along the identity is
the identity. -/
private def extIdExtensionByZeroAddEquiv (W : Scheme.{u}) (n : ℕ) :
    Ext (unitSheaf (X := W) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) (𝟙 W)).obj (unitSheaf (X := W) N)) n ≃+
    Ext (unitSheaf (X := W) N) (unitSheaf (X := W) N) n :=
  extPostcompAddEquiv N
    ((etaleModuleExtensionByZeroIdIso (ZMod N) W).app (unitSheaf (X := W) N)).hom n

/-- **`H⁰_c(W) ≅ ℤ/N` for `W` smooth irreducible of relative dimension zero**, through any
compactification: `W` is proper (`AlgebraicGeometry.isProper_of_smoothOfRelativeDimension_zero`),
so `H⁰_c(W) = H⁰(W, ℤ/N)` (independence of the compactification), and `W` is connected. -/
theorem nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero {W : Scheme.{u}}
    (p : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension 0 p] [TopologicalSpace.NoetherianSpace W]
    [IrreducibleSpace W] (jc : CompactificationOf (Over.mk p)) :
    Nonempty (Ext (unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj (unitSheaf (X := W) N))
        (2 * 0) ≃+ ZMod N) := by
  have := isProper_of_smoothOfRelativeDimension_zero p jc
  obtain ⟨e₁⟩ := nonempty_ext_addEquiv_of_compactifications N p jc
    (CompactificationOf.ofProper p) (unitSheaf (X := W) N) 0
  have : ConnectedSpace W :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ W).isConnected
  exact ⟨e₁.trans ((extIdExtensionByZeroAddEquiv N W 0).trans
    (extZeroUnitSheafAddEquivOfConnectedSpace N W))⟩

/-- **The complement of a dense open of a smooth variety has smaller dimension**: if `W` is
noetherian, irreducible and smooth of relative dimension `e + 1` over `k`, and `U ⊆ W` is a
nonempty open, then `W \ U` is the image of a closed immersion from a scheme of dimension at most
`e`. -/
private theorem exists_isClosedImmersion_range_compl_topologicalKrullDim_le (e : ℕ) {W : Scheme.{u}}
    (p : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension (e + 1) p]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W] (U : W.Opens)
    (hU : (U : Set W).Nonempty) :
    ∃ (Zc : Scheme.{u}) (iC : Zc ⟶ W), IsClosedImmersion iC ∧ Set.range iC = (U : Set W)ᶜ ∧
      topologicalKrullDim Zc ≤ (e : WithBot ℕ∞) := by
  obtain ⟨Zc, iC, hiC, hrange⟩ := exists_isClosedImmersion_range_eq ((U : Set W)ᶜ)
    U.isOpen.isClosed_compl
  refine ⟨Zc, iC, hiC, hrange, ?_⟩
  have hint : interior ((U : Set W)ᶜ) = ∅ := by
    rw [interior_compl, (U.isOpen.dense hU).closure_eq, Set.compl_univ]
  have : Nonempty W := ⟨hU.some⟩
  have hdimW : topologicalKrullDim W ≤ (e + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field (e + 1) p).le
  have hlt := topologicalKrullDim_lt_of_isClosed_of_interior_eq_empty U.isOpen.isClosed_compl
    hint hdimW iC.isEmbedding.isInducing hrange.le
  rcases hZ : topologicalKrullDim Zc with _ | y
  · exact bot_le
  · rw [hZ] at hlt
    have h0 : (y : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞) := hlt
    have h1 : y < (e : ℕ∞) + 1 := by exact_mod_cast WithBot.coe_lt_coe.1 h0
    exact WithBot.coe_le_coe.2 (Order.le_of_lt_add_one h1)

/-- The extension by zero of `ℤ/N_U` along `U ⊆ W ⟶ X` is the extension by zero along `j` of
the extension by zero of `ℤ/N_W` restricted to `U`. -/
private def extensionByZeroCompUnitSheafIso {W X : Scheme.{u}} (U : W.Opens) (j : W ⟶ X)
    [IsOpenImmersion j] :
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) (U.ι ≫ j)).obj (unitSheaf (X := U.toScheme) N) ≅
      (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj
        ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod N) U.ι).obj
          (unitSheaf (X := W) N)) :=
  (etaleModuleExtensionByZeroCompIso (ZMod N) U.ι j).app _ ≪≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).mapIso
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) U.ι).mapIso
        (((etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) U.ι).app
            (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))).symm ≪≫
          (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) U.ι).app (unitSheaf (X := W) N) :
          unitSheaf (X := U.toScheme) N ≅
            (etaleModuleRestriction.{u, 0} (ZMod N) U.ι).obj (unitSheaf (X := W) N)))

/-- **`H^{2e+2}_c(W) ≅ H^{2e}_c(S)` through an elementary fibration.** Let `W` be smooth
irreducible of relative dimension `e + 1` over a separably closed field `k`, noetherian, with a
compactification `j : W → X̄`, and let `f : U → S` be an elementary fibration on a nonempty open
`U ⊆ W` over `S` irreducible, affine and smooth of relative dimension `e`, compatibly with the
structure morphisms. If `R²f_! Λ ≅ Λ_S` for the compactifications of `f`, then for some
compactification `S → S̄` of dimension at most `e`,
`Ext^{2e+2}_X̄(Λ, j_! Λ_W) ≅ Ext^{2e}_S̄(Λ, (j_S)_! Λ_S)`. -/
theorem exists_ext_top_addEquiv_of_isElementaryFibration [IsSepClosed k] (e : ℕ)
    {W : Scheme.{u}} (p : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension (e + 1) p]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk p)) (U : W.Opens) (hU : (U : Set W).Nonempty)
    {S : Scheme.{u}} (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S)
    (hf : IsElementaryFibration f) [SmoothOfRelativeDimension e q] [IsAffine S]
    [IrreducibleSpace S] (hfq : f ≫ q = U.ι ≫ p)
    (hR2 : ∀ jf : CompactificationOf (Over.mk f), Nonempty
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U.toScheme) N))) ≅
        unitSheaf (X := S) N)) :
    ∃ (fS : S ⟶ Spec (.of k)) (jS : CompactificationOf (Over.mk fS)), fS = q ∧
      topologicalKrullDim jS.space ≤ (e : WithBot ℕ∞) ∧
      Nonempty (Ext (unitSheaf (X := jc.space) N)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj (unitSheaf (X := W) N))
          (2 * (e + 1)) ≃+
        Ext (unitSheaf (X := jS.space) N)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jS.immersion).obj
            (unitSheaf (X := S) N)) (2 * e)) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have : Smooth q := SmoothOfRelativeDimension.smooth e q
  have : IsSeparated p := by
    rw [← CompactificationOf.immersion_toBase jc]
    infer_instance
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiSeparatedSpace U.toScheme := NoetherianSpace.to_quasiSeparatedSpace
  have : CompactSpace jc.space := QuasiCompact.compactSpace_of_compactSpace jc.toBase
  have : IsLocallyNoetherian jc.space := LocallyOfFiniteType.isLocallyNoetherian jc.toBase
  have : IsNoetherian jc.space := ⟨⟩
  obtain ⟨Xbar, Z, j, fbar, iZ, hj, hjf, hsm, hproj, -, -, -, -, -, -, -⟩ :=
    hf.exists_compactification
  have := hsm
  have : IsProper fbar := isProper_of_isProjectiveMorphism fbar hproj
  let jf : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk fbar) (Over.homMk (U := Over.mk f) j hjf),
      ⟨hj, inferInstanceAs (IsProper fbar)⟩⟩
  have : IsSeparated f := by
    rw [← hjf]
    infer_instance
  have : LocallyOfFiniteType f := by
    rw [← hjf]
    infer_instance
  have hfib : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ (1 : WithBot ℕ∞) := fun y =>
    topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 fbar y
  obtain ⟨c⟩ : Nonempty (CompactificationOf (Over.mk q)) := IsCofiltered.nonempty
  let jS := (c.restrictOpen (𝟙 S)).restrictClosed (𝟙 S)
  have : SmoothOfRelativeDimension e (𝟙 S ≫ 𝟙 S ≫ q) := by
    simp only [Category.id_comp]
    infer_instance
  have hdimS : topologicalKrullDim jS.space ≤ (e : WithBot ℕ∞) :=
    topologicalKrullDim_restrictClosed_space_le q c (𝟙 S) (𝟙 S) e
  obtain ⟨Zc, iC, hiC, hrange, hdimZ⟩ :=
    exists_isClosedImmersion_range_compl_topologicalKrullDim_le e p U hU
  have hiU : Set.range U.ι.base = (Set.range iC.base)ᶜ := by
    rw [hrange, compl_compl, Scheme.Opens.range_ι]
  have hbij := bijective_ext_extensionByZero_counit_of_closed jc U iC hiU e hdimZ
    (unitSheaf (X := W) N) (2 * (e + 1)) (by omega)
  obtain ⟨eL⟩ := nonempty_ext_top_addEquiv_of_higherDirectImage_two_iso (𝟙 S ≫ 𝟙 S ≫ q) jS N f
    (by simpa using hfq) jf (jc.restrictOpen U.ι) e hdimS hfib (hR2 jf)
  let eT := extensionByZeroCompUnitSheafIso N U jc.immersion
  let φ := (Ext.mk₀ ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).map
    ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) U.ι).counit.app
      (unitSheaf (X := W) N)))).postcomp (unitSheaf (X := jc.space) N) (add_zero (2 * (e + 1)))
  exact ⟨𝟙 S ≫ 𝟙 S ≫ q, jS, by simp, hdimS, ⟨(AddEquiv.ofBijective φ hbij).symm.trans
    ((extPostcompAddEquiv N eT.hom (2 * (e + 1))).symm.trans eL)⟩⟩

variable (k) in
/-- **Dense elementary fibrations** (SGA 4, Exposé XI, Proposition 3.3): every smooth irreducible
`X` of relative dimension `d ≥ 1` over `k` contains a nonempty open `U` which is an elementary
fibration `f : U → S` over an irreducible affine `S` smooth of relative dimension `d - 1`,
compatibly with the structure morphisms. This is the statement whose reduction to the generic
fibre is `AlgebraicGeometry.exists_dense_isElementaryFibration_of_genericFibre`. -/
def ExistsDenseElementaryFibration : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d p]
    [IrreducibleSpace X], 1 ≤ d →
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      (U : Set X).Nonempty ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ IrreducibleSpace S ∧ f ≫ q = U.ι ≫ p

variable (k) in
/-- **`R²f_! ℤ/N ≅ ℤ/N` for an elementary fibration** `f : U → S` over `S` affine and smooth over
`k`, for every compactification of `f`, when `N` is invertible in `k`. -/
def HigherDirectImageTwoOfElementaryFibration : Prop :=
  IsUnit (N : k) → ∀ (U S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U ⟶ S) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S], IsElementaryFibration f →
    ∀ jf : CompactificationOf (Over.mk f), Nonempty
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod N)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := U) N))) ≅
        unitSheaf (X := S) N)

/-- **`H^{2e}_c(W, ℤ/N) ≅ ℤ/N`** for `N` invertible in `k` and `W` smooth irreducible of relative
dimension `e` over a separably closed field `k`, noetherian, through any compactification: by
induction on `e`, through a dense elementary fibration `U → S` (`H^{2e}_c(W) ≅ H^{2e-2}_c(S)`,
`Stacks.EtaleCohomology.exists_ext_top_addEquiv_of_isElementaryFibration`), the case `e = 0` being
`Stacks.EtaleCohomology.nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero`. -/
theorem nonempty_ext_top_addEquiv_zmod [IsSepClosed k] (hN : IsUnit (N : k))
    (hfib : ExistsDenseElementaryFibration k)
    (hR2 : HigherDirectImageTwoOfElementaryFibration k N) :
    ∀ (e : ℕ) (W : Scheme.{u}) (p : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e p]
      [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk p)),
      Nonempty (Ext (unitSheaf (X := jc.space) N)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj (unitSheaf (X := W) N))
          (2 * e) ≃+ ZMod N) := by
  intro e
  induction e with
  | zero =>
    intro W p _ _ _ jc
    exact nonempty_ext_zero_addEquiv_zmod_of_smoothOfRelativeDimension_zero N p jc
  | succ e ih =>
    intro W p _ _ _ jc
    obtain ⟨U, S, q, f, hU, hf, hq, hS, hSi, hfq⟩ := hfib W p (e + 1) (by omega)
    rw [Nat.add_sub_cancel] at hq
    have := hq
    have := hS
    have := hSi
    have : Smooth q := SmoothOfRelativeDimension.smooth e q
    have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
    have : IsNoetherian S := ⟨⟩
    obtain ⟨fS, jS, hfS, -, ⟨eW⟩⟩ := exists_ext_top_addEquiv_of_isElementaryFibration N e p jc U
      hU q f hf hfq (hR2 hN U.toScheme S q f e hf)
    subst hfS
    obtain ⟨eS⟩ := ih S _ jS
    exact ⟨eW.trans eS⟩

/-- **`H^{2d}(Y, ℤ/ℓ^{m+1}) ≅ ℤ/ℓ^{m+1}`** for `Y` connected, smooth of relative dimension `d` and
proper over an algebraically closed field: `Y` is its own compactification
(`Stacks.EtaleCohomology.nonempty_ext_top_addEquiv_zmod`), given dense elementary fibrations and
`R²f_! ℤ/ℓ^{m+1} ≅ ℤ/ℓ^{m+1}` for them. -/
theorem natCard_ext_unitSheaf_top_pow (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [IsAlgClosed k] (hℓ : IsUnit (ℓ : k)) {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g]
    (d : ℕ) [SmoothOfRelativeDimension d g] [ConnectedSpace Y] (m : ℕ)
    (hfib : ExistsDenseElementaryFibration k)
    (hR2 : HigherDirectImageTwoOfElementaryFibration k (ℓ ^ (m + 1))) :
    Nonempty (Ext (unitSheaf (X := Y) (ℓ ^ (m + 1))) (unitSheaf (ℓ ^ (m + 1))) (2 * d) ≃+
      ZMod (ℓ ^ (m + 1))) := by
  have : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : Smooth g := SmoothOfRelativeDimension.smooth d g
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian Y := ⟨⟩
  have : IrreducibleSpace Y := irreducibleSpace_of_smooth_of_connectedSpace g
  have hN : IsUnit (((ℓ ^ (m + 1) : ℕ) : k)) := by
    push_cast
    exact hℓ.pow _
  obtain ⟨e₁⟩ := nonempty_ext_top_addEquiv_zmod (ℓ ^ (m + 1)) hN hfib hR2 d Y g
    (CompactificationOf.ofProper g)
  exact ⟨(extIdExtensionByZeroAddEquiv _ Y (2 * d)).symm.trans e₁⟩

end Stacks.EtaleCohomology

end
