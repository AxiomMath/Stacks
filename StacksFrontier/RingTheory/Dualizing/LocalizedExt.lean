module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# Localization of the Ext modules out of a finite module

Let `A` be a Noetherian ring, `T` a multiplicative subset, `M` a finite `A`-module and `K` a
bounded-below object of the derived category of `A`-modules.  Forming `Ext^i(M, K)` commutes with
localization at `T`: the localization of the `A`-module `Ext_A^i(M, K)` is the `T⁻¹A`-module
`Ext^i` formed from the localizations of `M` and of `K`.  The statement is recorded in the form
in which it is used, as the equivalence of the nonvanishing of the two modules.

The identification is also recorded one level down, on the derived Hom complex itself and
**naturally in the module**: the derived extension of scalars of `RHom_A(M, K)` to `T⁻¹A` is
`RHom_{T⁻¹A}(M_T, K_T)`, compatibly with every map of finite `A`-modules.  That naturality is
what the uniformity argument of [Stacks, Tag 0EFX] needs, where the vanishing of a map of the
finite modules `Ext^j_A(IⁿM, ω)` has to be read off the vanishing of the corresponding map over
`A_𝔮`, for a varying `n`.

## Main definitions

* `Dualizing.localizedSingleIso` — total derived extension of scalars carries a module placed in
  degree zero to its localization placed in degree zero.
* `Dualizing.localizedDerivedHomIso` — total derived extension of scalars carries
  `RHom_A(M, K)` to `RHom_{T⁻¹A}(M_T, K_T)`, for `M` finite and `K` bounded below.
* `Dualizing.localizedDerivedHomHomologyIso` — the localization at `T` of the `A`-module
  `H^i(RHom_A(M, K))` is `H^i(RHom_{T⁻¹A}(M_T, K_T))`.
* `Dualizing.localizedExtLinearEquivOfDerivedHom` — the localization at `T` of `Ext^i_A(M, K)` is
  `Ext^i_{T⁻¹A}(M_T, K_T)`, linearly over `T⁻¹A`.

## Main results

* `Dualizing.localized_ext_nontrivial_iff` — the localization at `T` of `Ext_A^i(M, K)` is nonzero
  exactly when the corresponding `Ext` module over `T⁻¹A` is nonzero.
* `Dualizing.isIso_derivedHomBaseChange_localization` — the base-change map for derived Hom is
  invertible along `A → T⁻¹A` when the source is a finite module in degree zero.
* `Dualizing.localizedSingleIso_naturality`, `Dualizing.localizedSingleIso_inv_naturality`,
  `Dualizing.localizedDerivedHomIso_naturality`,
  `Dualizing.localizedDerivedHomHomologyIso_naturality` and
  `Dualizing.localizedExtLinearEquivOfDerivedHom_naturality` — the comparisons are natural in the
  module: localizing a precomposition map gives the precomposition map over `T⁻¹A`.

## Implementation notes

The identification comes from the base-change map for derived Hom, which is invertible along the
flat map `A → T⁻¹A` because `M` placed in degree zero is pseudo-coherent and `K` is bounded below.
Both `Ext` modules are compared with the cohomology of the derived Hom complex, over `A` and over
`T⁻¹A` respectively, and the cohomology of the derived extension of scalars of a complex of
`A`-modules along `A → T⁻¹A` is the localization of its cohomology.

`Dualizing.localizedDerivedHomHomologyIso` is the comparison at the level of the modules the
uniformity paragraph of [Stacks, Tag 0EFX] spreads out: for `K` a dualizing complex and `M`
finite, `H^i(RHom_A(M, K))` is a finite `A`-module by
`Dualizing.dualizingDerivedHom_finiteCohomology`, and `Dualizing.extIntoOmegaAtLinearEquiv`
identifies it with `Ext^i_A(M, K)` compatibly with precomposition
(`Dualizing.extIntoOmegaAtLinearEquiv_naturality`).  Composing that identification, over `A` and
over `T⁻¹A`, with the isomorphism here is what turns a statement about the localized `Ext` modules
into one about the localized cohomology modules, so the naturality is recorded at the cohomology
level, where the comparison is assembled and where the finiteness lives, and the `Ext` form is
read off it.

The naturality statements are proved in term mode, with every associativity step written as an
explicit application of `CategoryTheory.Category.assoc`.  In this import closure the instances
carried by a morphism of the derived category of modules over a localization are expensive enough
that `rw` fails to match even the bare associativity pattern, while the same step as a term, whose
arguments pin the instances, elaborates at once.  For the same reason
`Dualizing.localizedExtLinearEquivOfDerivedHom_naturality` goes through
`Dualizing.localizedExtLinearEquivOfDerivedHom_apply_mk` rather than unfolding the equivalence
inside the naturality proof: unifying the unfolded three-factor composite against the folded one
exhausts the recursion budget, while naming the computation on a fraction keeps every unification
small.

## References

* [Stacks Project, Tag 0E1V](https://stacks.math.columbia.edu/tag/0E1V), the base-change map for
  derived Hom.
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX), whose uniformity
  paragraph consumes the naturality.
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- Base change of derived Hom out of a finite module and into a bounded-below complex is an
isomorphism along the flat map `A → T⁻¹A`. -/
private theorem localization_derivedHomBaseChange_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {T : Submonoid A} {M : Type (max v u)}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hKge : ∃ b : ℤ, K.IsGE b)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u,
      max v u, u}
      (algebraMap A (Localization T)))
    (comparison : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap A (Localization T))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [hD : D.functor.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A)
        (ComplexShape.up ℤ))] :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, v}
      (algebraMap A (Localization T))
      D.functor comparison
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A M)) K) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  have hXpc : StacksDraft.PseudoCoherence.IsPseudoCoherent X := by
    show StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := A) M
    exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      X 0 M).2.2.mpr inferInstance
  exact Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, v}
    (algebraMap A (Localization T))
    D.functor comparison X K
    (Or.inr (Or.inr (Or.inl
      ⟨RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization T) T),
        hXpc, hKge⟩)))

/-- **Base change of derived Hom at a localization.** Base change of derived Hom out of a finite
module and into a bounded-below complex is an isomorphism along the flat map `A → T⁻¹A`. -/
public alias isIso_derivedHomBaseChange_localization := localization_derivedHomBaseChange_isIso

/-- The localization at `T` of `Ext_A^i(M, K)` is nonzero exactly when the corresponding Ext
module over `T⁻¹A`, formed from the localizations of `M` and of `K`, is nonzero. -/
theorem localized_ext_nontrivial_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {T : Submonoid A}
    {M : Type (max v u)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) :
    Nontrivial (LocalizedModule T (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M)) K i)) ↔
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{max v u} T).obj (ModuleCat.of A M)))
      ((ModuleCat.localizedModuleFunctor.{max v u} T).mapDerivedCategory.obj K) i) := by
  classical
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  let G := ModuleCat.localizedModuleFunctor.{max v u} T
  let Xloc := (DerivedCategory.singleFunctor (ModuleCat.{max v u} (Localization T)) 0).obj
    (G.obj (ModuleCat.of A M))
  let Kloc := G.mapDerivedCategory.obj K
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u}
    (algebraMap A (Localization T))
  let HA := (Dualizing.dualizingDerivedHomFunctor.{u, max u v} A K).obj (.op X)
  let eA : DerivedCategory.Ext X K i ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj HA) := by
    show (X ⟶ K⟦i⟧) ≃ₗ[A] _
    exact Dualizing.extIntoOmegaAtLinearEquiv.{u, max u v} A K i (ModuleCat.of A M)
  let eX : D.functor.obj X ≅ Xloc :=
    localizationDerivedIso T D X ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A M)
  let eK : D.functor.obj K ≅ Kloc := localizationDerivedIso T D K
  let comparison : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap A (Localization T))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  let β := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, v}
    (algebraMap A (Localization T)) D.functor comparison X K
  have : IsIso β := localization_derivedHomBaseChange_isIso (T := T) (M := M) K hKge D comparison
  let Hloc := (Dualizing.dualizingDerivedHomFunctor.{u, max u v}
    (Localization T) Kloc).obj (.op Xloc)
  let eHom : D.functor.obj HA ≅ Hloc := by
    show D.functor.obj ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom A).obj
      (.op X, K)) ≅ _
    exact asIso β ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom (Localization T)).mapIso
        (eX.symm.op.prod eK)
  let eH : (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (Localization T)) i).obj
        (D.functor.obj HA)) ≅
    ModuleCat.of A (LocalizedModule T
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj HA)) := by
    simpa only [Functor.comp_obj, CochainComplex.DerivedTensor.localizedModuleFunctor] using
      (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, max v u}
        (R := A) (A := Localization T) (S := T) i).app HA
  let eA_loc : LocalizedModule T
      (DerivedCategory.Ext X K i) ≃ₗ[(Localization T)] LocalizedModule T
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj HA) :=
    IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T (DerivedCategory.Ext X K i))
      (LocalizedModule.mkLinearMap T
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj HA)) (Localization T) eA
  let eB : DerivedCategory.Ext Xloc Kloc i ≃ₗ[(Localization T)]
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (Localization T)) i).obj Hloc) := by
    show (Xloc ⟶ Kloc⟦i⟧) ≃ₗ[(Localization T)] _
    exact Dualizing.extIntoOmegaAtLinearEquiv.{u, max u v} (Localization T) Kloc i
      (G.obj (ModuleCat.of A M))
  exact (eA_loc.toEquiv.trans (eH.symm.toLinearEquiv.toEquiv.trans
    (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} (Localization T)) i).mapIso
      eHom).toLinearEquiv.toEquiv.trans eB.symm.toEquiv))).nontrivial_congr

/-! ### The localized `Ext` module, and its naturality in the source -/

section Naturality

/-- The type of the comparison natural transformation of a model of total derived extension of
scalars along `A → T⁻¹A`: a transformation from the localization of the model to extension of
scalars on cochain complexes followed by localization. -/
public abbrev DerivedExtensionScalarsComparison {A : Type u} [CommRing A] (T : Submonoid A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T))) : Type _ :=
  DerivedCategory.Q ⋙ D.functor ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- **The localization of a module placed in degree zero.** Applying a model of total derived
extension of scalars along `A → T⁻¹A` to `M` placed in degree zero gives the localization `M_T`
placed in degree zero. -/
public noncomputable def localizedSingleIso {A : Type u} [CommRing A] (T : Submonoid A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)))
    (M : ModuleCat.{u} A) :
    D.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} T).obj M) :=
  localizationDerivedIso.{u, u} T D ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≪≫
    ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategorySingleFunctor 0).app M

/-- `Dualizing.localizedSingleIso` is natural in the module. -/
public theorem localizedSingleIso_naturality {A : Type u} [CommRing A] (T : Submonoid A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)))
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    D.functor.map ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f) ≫
        (localizedSingleIso.{u} T D N).hom =
      (localizedSingleIso.{u} T D M).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
          ((ModuleCat.localizedModuleFunctor.{u} T).map f) := by
  simp only [localizedSingleIso, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% (localizationDerivedIso_naturality.{u, u} T D
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f))]
  exact congrArg _ (((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategorySingleFunctor
    (0 : ℤ)).hom.naturality f)

/-- `Dualizing.localizedSingleIso` is natural in the module, read on the inverse. -/
public theorem localizedSingleIso_inv_naturality {A : Type u} [CommRing A] (T : Submonoid A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)))
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (localizedSingleIso.{u} T D M).inv ≫
        D.functor.map ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
          ((ModuleCat.localizedModuleFunctor.{u} T).map f) ≫
        (localizedSingleIso.{u} T D N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact localizedSingleIso_naturality.{u} T D f

/-- The contravariant derived-Hom functor against a fixed object acts as the derived internal-Hom
bifunctor with the identity in its second variable. -/
private theorem dualizingDerivedHomFunctor_map_eq {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    {X Y : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ} (g : X ⟶ Y) :
    (Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map g =
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).map (g, 𝟙 K) :=
  rfl

/-- **Base change of derived Hom out of a finite module at a localization.** For a finite
`A`-module `M` and a bounded-below `K`, the derived extension of scalars of `RHom_A(M, K)` to
`T⁻¹A` is `RHom_{T⁻¹A}(M_T, K_T)`. -/
public noncomputable def localizedDerivedHomIso {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (K : DerivedCategory (ModuleCat.{u} A))
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)))
    (comparison : DerivedExtensionScalarsComparison.{u} T D)
    [hD : D.functor.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (M : ModuleCat.{u} A) [Module.Finite A M] (hKge : ∃ b : ℤ, K.IsGE b) :
    D.functor.obj ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) ≅
      (Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
          ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
          ((ModuleCat.localizedModuleFunctor.{u} T).obj M))) :=
  @asIso _ _ _ _
      (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
        (algebraMap A (Localization T)) D.functor comparison
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) K)
      (isIso_derivedHomBaseChange_localization.{u, u} (T := T) (M := M) K hKge D comparison) ≪≫
    (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (Localization T)).mapIso
      ((localizedSingleIso.{u} T D M).symm.op.prod (localizationDerivedIso.{u, u} T D K))

/-- `Dualizing.localizedDerivedHomIso` is natural in the finite module: the square comparing the
derived extension of scalars of `RHom_A(-, K)` with `RHom_{T⁻¹A}((-)_T, K_T)` commutes for every
map of finite modules. -/
public theorem localizedDerivedHomIso_naturality {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (K : DerivedCategory (ModuleCat.{u} A))
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)))
    (comparison : DerivedExtensionScalarsComparison.{u} T D)
    [hD : D.functor.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (hKge : ∃ b : ℤ, K.IsGE b)
    {M N : ModuleCat.{u} A} [Module.Finite A M] [Module.Finite A N] (f : M ⟶ N) :
    D.functor.map ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op) ≫
        (localizedDerivedHomIso.{u} T K D comparison M hKge).hom =
      (localizedDerivedHomIso.{u} T K D comparison N hKge).hom ≫
        (Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
            ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
            ((ModuleCat.localizedModuleFunctor.{u} T).map f)).op := by
  have h : ∀ (P : ModuleCat.{u} A) [Module.Finite A P],
      (localizedDerivedHomIso.{u} T K D comparison P hKge).hom =
      Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
          (algebraMap A (Localization T)) D.functor comparison
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj P) K ≫
        (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (Localization T)).map
          ((localizedSingleIso.{u} T D P).inv.op, (localizationDerivedIso.{u, u} T D K).hom) :=
    fun _ _ => rfl
  rw [h M, h N, dualizingDerivedHomFunctor_map_eq, dualizingDerivedHomFunctor_map_eq]
  refine Eq.trans
    (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality_assoc.{u, u, u}
      (algebraMap A (Localization T)) D.functor comparison
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f) (𝟙 K) _)
    (Eq.trans (congrArg (CategoryStruct.comp _) ?_) (Category.assoc _ _ _).symm)
  refine Eq.trans ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u}
      (Localization T)).map_comp _ _).symm
    (Eq.trans (congrArg (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u}
        (Localization T)).map ?_)
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u}
        (Localization T)).map_comp _ _))
  refine Prod.ext ?_ ?_
  · exact congrArg Quiver.Hom.op (localizedSingleIso_inv_naturality.{u} T D f)
  · show D.functor.map (𝟙 K) ≫ _ = _ ≫ 𝟙 _
    exact Eq.trans (congrArg (fun z => CategoryStruct.comp z
          (localizationDerivedIso.{u, u} T D K).hom) (D.functor.map_id K))
      (Eq.trans (Category.id_comp _) (Category.comp_id _).symm)

/-! ### The localized cohomology of derived Hom -/

/-- The chosen model of total derived extension of scalars along `A → T⁻¹A`, together with its
comparison transformation, is the model the localization-of-cohomology isomorphism
`CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso` is stated for. -/
public noncomputable abbrev localizationTotalDerived {A : Type u} [CommRing A]
    (T : Submonoid A) :
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization T)) :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization T))

/-- **The localization of the cohomology of derived Hom out of a finite module.** For a finite
`A`-module `M` and a bounded-below object `K` of `D(A)`, the localization at `T` of the finite
`A`-module `H^i(RHom_A(M, K))` is `H^i(RHom_{T⁻¹A}(M_T, K_T))`, read as an `A`-module through
restriction of scalars along `A → T⁻¹A`. -/
public noncomputable def localizedDerivedHomHomologyIso {A : Type u} [CommRing A]
    [IsNoetherianRing A] (T : Submonoid A) (K : DerivedCategory (ModuleCat.{u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) (M : ModuleCat.{u} A) [Module.Finite A M] :
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} T).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) ≅
      (ModuleCat.restrictScalars (algebraMap A (Localization T))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
              ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
              ((ModuleCat.localizedModuleFunctor.{u} T).obj M))))) :=
  ((CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, u}
      (R := A) (A := Localization T) (S := T) i).app
    ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
      (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap A (Localization T))).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).mapIso
        (localizedDerivedHomIso.{u} T K (localizationTotalDerived.{u} T)
          (localizationTotalDerived.{u} T).comparison
          (hD := (localizationTotalDerived.{u} T).isLeftDerived) M hKge))

/-- **`Dualizing.localizedDerivedHomHomologyIso` is natural in the finite module.** This is the
naturality the uniformity paragraph in the proof of [Stacks, Tag 0EFX] runs on: the vanishing of
a transition map of the finite `A`-modules `H^j(RHom_A(IⁿM, ω))` after localization at a prime
`𝔮` is the vanishing of the corresponding map over `A_𝔮`, and the correspondence is compatible
with the maps of the tower. -/
public theorem localizedDerivedHomHomologyIso_naturality {A : Type u} [CommRing A]
    [IsNoetherianRing A] (T : Submonoid A) (K : DerivedCategory (ModuleCat.{u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) {M N : ModuleCat.{u} A}
    [Module.Finite A M] [Module.Finite A N] (f : M ⟶ N) :
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} T).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
            ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op)) ≫
        (localizedDerivedHomHomologyIso.{u} T K hKge i M).hom =
      (localizedDerivedHomHomologyIso.{u} T K hKge i N).hom ≫
        (ModuleCat.restrictScalars (algebraMap A (Localization T))).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map
            ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
                ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).map
              ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
                ((ModuleCat.localizedModuleFunctor.{u} T).map f)).op)) := by
  have hΘ := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, u}
    (R := A) (A := Localization T) (S := T) i).inv.naturality
      ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op)
  have h : ∀ (P : ModuleCat.{u} A) [Module.Finite A P],
      (localizedDerivedHomHomologyIso.{u} T K hKge i P).hom =
      ((CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, u}
        (R := A) (A := Localization T) (S := T) i).inv.app
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj P)))) ≫
        (ModuleCat.restrictScalars (algebraMap A (Localization T))).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map
            (localizedDerivedHomIso.{u} T K (localizationTotalDerived.{u} T)
              (localizationTotalDerived.{u} T).comparison
              (hD := (localizationTotalDerived.{u} T).isLeftDerived) P hKge).hom) :=
    fun _ _ => rfl
  rw [h M, h N]
  refine Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans (congrArg (fun z => CategoryStruct.comp z
        ((ModuleCat.restrictScalars (algebraMap A (Localization T))).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map
            (localizedDerivedHomIso.{u} T K (localizationTotalDerived.{u} T)
              (localizationTotalDerived.{u} T).comparison
              (hD := (localizationTotalDerived.{u} T).isLeftDerived) M hKge).hom))) hΘ)
      (Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg (CategoryStruct.comp _) ?_)
        (Category.assoc _ _ _).symm)))
  refine Eq.trans ((ModuleCat.restrictScalars (algebraMap A (Localization T))).map_comp _ _).symm
    (Eq.trans (congrArg (ModuleCat.restrictScalars (algebraMap A (Localization T))).map
      (Eq.trans ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map_comp
          _ _).symm
        (Eq.trans (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T))
            i).map (localizedDerivedHomIso_naturality.{u} T K (localizationTotalDerived.{u} T)
              (localizationTotalDerived.{u} T).comparison
              (hD := (localizationTotalDerived.{u} T).isLeftDerived) hKge f))
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map_comp _ _))))
      ((ModuleCat.restrictScalars (algebraMap A (Localization T))).map_comp _ _))

/-! ### Localizing `Ext` out of a finite module, naturally in the module -/

/-- **Localizing `Ext` out of a finite module, as a linear equivalence.** For a Noetherian ring
`A`, a submonoid `T`, a finite `A`-module `M` and a bounded-below `K` of `D(A)`, the localization
of `Ext^i_A(M, K)` at `T` is `Ext^i_{T⁻¹A}(T⁻¹M, T⁻¹K)`, linearly over `T⁻¹A`.

The identification is `Dualizing.localizedDerivedHomHomologyIso` conjugated by the Ext--cohomology
comparison `Dualizing.extIntoOmegaAtLinearEquiv` over `A` and over `T⁻¹A`, and that is what makes
it natural in `M`, which is `Dualizing.localizedExtLinearEquivOfDerivedHom_naturality`. -/
public noncomputable def localizedExtLinearEquivOfDerivedHom
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) :
    LocalizedModule T (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i) ≃ₗ[
        Localization T]
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))
      ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i := by
  letI : Module A ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).obj
      ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
          ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
          ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))))) :=
    Module.compHom _ (algebraMap A (Localization T))
  haveI : IsScalarTower A (Localization T)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
            ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
            ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module A (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))
      ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i) :=
    Module.compHom _ (algebraMap A (Localization T))
  haveI : IsScalarTower A (Localization T) (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))
      ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (((IsLocalizedModule.mapEquiv T
        (LocalizedModule.mkLinearMap T (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i))
        (LocalizedModule.mkLinearMap T
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
              (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A M)))))) (Localization T)
        (Dualizing.extIntoOmegaAtLinearEquiv.{u, u} A K i
          (ModuleCat.of A M))).restrictScalars A).trans
      ((localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A M)).toLinearEquiv.trans
        ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
          ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
          ((ModuleCat.localizedModuleFunctor.{u} T).obj
            (ModuleCat.of A M))).symm.restrictScalars A))).extendScalarsOfIsLocalization T
    (Localization T)

/-- `Dualizing.localizedExtLinearEquivOfDerivedHom` on a fraction, written out through its three
factors. -/
private theorem localizedExtLinearEquivOfDerivedHom_apply_mk
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ)
    (y : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i)
    (s : T) :
    localizedExtLinearEquivOfDerivedHom.{u} T M K hKge i (LocalizedModule.mk y s) =
      (Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M))).symm
        ((localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A M)).hom.hom
          (LocalizedModule.mk
            ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} A K i (ModuleCat.of A M)) y) s)) :=
  congrArg (fun z => (Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M))).symm
      ((localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A M)).hom.hom z))
    (LocalizedModule.map_mk _ _ _ _)

/-- **The localization of `Ext` out of a finite module is natural in the module.** For a map
`f : M ⟶ N` of finite `A`-modules, localizing the precomposition map
`Ext^i_A(N, K) ⟶ Ext^i_A(M, K)` gives the precomposition map
`Ext^i_{T⁻¹A}(N_T, K_T) ⟶ Ext^i_{T⁻¹A}(M_T, K_T)`.

This is the square the uniformity paragraph in the proof of [Stacks, Tag 0EFX] runs on: it reads
the vanishing of a transition map of the finite modules `Ext^j_A(IⁿM, ω)` after localization at a
prime `𝔮` as the vanishing of the corresponding map over `A_𝔮`. -/
public theorem localizedExtLinearEquivOfDerivedHom_naturality
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (f : ModuleCat.of A M ⟶ ModuleCat.of A N)
    (K : DerivedCategory (ModuleCat.{u} A)) (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ)
    (x : LocalizedModule T (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N)) K i)) :
    localizedExtLinearEquivOfDerivedHom.{u} T M K hKge i
        (LocalizedModule.map T
          (Linear.leftComp A
            ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).obj K)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f)) x) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
          ((ModuleCat.localizedModuleFunctor.{u} T).map f) ≫
        localizedExtLinearEquivOfDerivedHom.{u} T N K hKge i x := by
  induction x using LocalizedModule.induction_on with
  | _ y s =>
    simp only [LocalizedModule.map_mk, Linear.leftComp_apply]
    have hA := Dualizing.extIntoOmegaAtLinearEquiv_naturality.{u, u} A K i f y
    have hB := Dualizing.extIntoOmegaAtLinearEquiv_naturality.{u, u} (Localization T)
      ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
      ((ModuleCat.localizedModuleFunctor.{u} T).map f)
      ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A N))).symm
        ((localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A N)).hom.hom
          (LocalizedModule.mk
            ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} A K i (ModuleCat.of A N)) y) s)))
    have hCmk : ∀ (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
            (.op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A N))))) (t : T),
        ((CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} T).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op))).hom
          (LocalizedModule.mk z t) =
          LocalizedModule.mk (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f).op)).hom z) t :=
      fun _ _ => LocalizedModule.map_mk _ _ _ _
    have hD := ConcreteCategory.congr_hom
      (localizedDerivedHomHomologyIso_naturality.{u} T K hKge i f)
      (LocalizedModule.mk
        ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} A K i (ModuleCat.of A N)) y) s)
    refine Eq.trans (localizedExtLinearEquivOfDerivedHom_apply_mk.{u} T M K hKge i
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f ≫ y) s) ?_
    refine Eq.trans ?_ (congrArg (fun w =>
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
          ((ModuleCat.localizedModuleFunctor.{u} T).map f) ≫ w)
      (localizedExtLinearEquivOfDerivedHom_apply_mk.{u} T N K hKge i y s).symm)
    refine (Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M))).injective ?_
    refine Eq.trans ((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M))).apply_symm_apply _) ?_
    refine Eq.trans (congrArg (fun z =>
      (localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A M)).hom.hom
        (LocalizedModule.mk z s))
      hA) ?_
    refine Eq.trans (congrArg (fun z =>
      (localizedDerivedHomHomologyIso.{u} T K hKge i (ModuleCat.of A M)).hom.hom z)
      (hCmk _ s).symm) ?_
    refine Eq.trans hD ?_
    refine Eq.trans (congrArg (fun z =>
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization T)) i).map
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Localization T)
          ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).map
            ((ModuleCat.localizedModuleFunctor.{u} T).map f)).op)).hom z)
      (((Dualizing.extIntoOmegaAtLinearEquiv.{u, u} (Localization T)
        ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A N))).apply_symm_apply
          _).symm)) ?_
    exact hB.symm

end Naturality

end Dualizing

end
