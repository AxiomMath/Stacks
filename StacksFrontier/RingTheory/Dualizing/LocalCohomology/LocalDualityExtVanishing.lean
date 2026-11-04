module

public import StacksFrontier.Homology.DerivedComplete.NoetherianCompletionUnitInjective
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.Ext.DerivedFiniteness

/-!
# Transporting the vanishing of local cohomology to the dual Ext modules

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field and let `Z = V(𝔪)`. For a morphism
`g : K' ⟶ K` of `D(A)` the degree-`-i` Ext map `Ext^{-i}_A(K, ω) ⟶ Ext^{-i}_A(K', ω)` is
precomposition with `g`, that is `u ↦ g ≫ u` on morphisms `K ⟶ ω⟦-i⟧`. The theorem below says
that this map vanishes as soon as `H^i_Z(g)` does.

This is the first move of the uniformity paragraph in the proof of [Stacks, Tag 0EFX]: there the
vanishing of the transition maps of `{H^i_𝔮((IⁿM)_𝔮)}` is carried over to the finite modules
`Ext^j_A(IⁿM, ω)`, on which — unlike on local cohomology, which is not finite — a vanishing can
be spread out over a neighbourhood of `𝔮`.

Two inputs make the transport possible.

* Local duality **natural in `K`**, `Dualizing.LocalDuality.exists_localDualityExtNatEquiv`: the
  isomorphisms `H⁰(RHom_A(K, ω⟦-i⟧)^∧) ≅ Hom_A(H^i_Z(K), E)` come with the commuting square for
  every `g : K' ⟶ K`. The square turns the vanishing of `H^i_Z(g)` into the vanishing of the
  precomposition map on `H⁰` of the *completed* derived Hom.
* The injectivity of the derived completion unit on cohomology,
  `AdicCompletionCohomology.injective_homology_derivedCompletionUnit`, which brings that
  vanishing back down from the completion to `H⁰(RHom_A(K', ω⟦-i⟧)) = Ext^{-i}_A(K', ω)`. The
  naturality square alone does not give this step: it concerns the completed modules only.

## Main results

* `Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero` — the transport:
  if `H^i_Z(g) = 0` then `g ≫ u = 0` for every `u : K ⟶ ω⟦-i⟧`.
* `Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero_of_bounded` — the
  same, with the finiteness of the cohomology of `RHom_A(K', ω⟦-i⟧)` replaced by boundedness and
  finiteness of the cohomology of `K'` and of `ω⟦-i⟧` separately.

## Implementation notes

The conclusion is stated as the vanishing of `u ↦ g ≫ u` on `K ⟶ ω⟦-i⟧` rather than on a module
called `Ext`: those morphism groups *are* the Ext modules — this is
`extHomologyZeroLinearEquiv` composed with `DerivedCategory.Ext` — and stating the
conclusion on morphisms keeps the statement free of the identification.

The finiteness of the cohomology modules of `RHom_A(K', ω⟦-i⟧)` is a hypothesis. It is the
hypothesis under which Stacks 0A06 identifies `H⁰` of a derived completion with an adic
completion, and it holds in the intended application, where `K'` is a finite module placed in
degree zero and `ω` is dualizing, so that those cohomology modules are the finite modules
`Ext^j_A(K', ω)`. It is a finiteness side condition on the data and not a step of the proof of
[Stacks, Tag 0EFX].

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing.LocalDuality

variable (A : Type u) [CommRing A]

/-- **The vanishing of local cohomology transported to the dual Ext modules.** Let `(A, 𝔪, κ)`
be a Noetherian local ring, let `f` generate `𝔪`, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field and let `Z = V(𝔪)`. Let `g : K' ⟶ K` be a
morphism of `D(A)` whose induced map `H^i_Z(K') ⟶ H^i_Z(K)` is zero, and suppose the cohomology
modules of `RHom_A(K', ω⟦-i⟧)` are finite. Then precomposition with `g`, which is the Ext map
`Ext^{-i}_A(K, ω) ⟶ Ext^{-i}_A(K', ω)`, is zero: `g ≫ u = 0` for every `u : K ⟶ ω⟦-i⟧`.

*Argument.* Let `θ` be the family of local duality isomorphisms
`H⁰(RHom_A(-, ω⟦-i⟧)^∧) ≅ Hom_A(H^i_Z(-), E)` of
`Dualizing.LocalDuality.exists_localDualityExtNatEquiv`, natural in the object. Send `u` to
`H⁰(RHom_A(K, ω⟦-i⟧)^∧)` along the derived completion unit; the naturality square identifies the
image of that class under precomposition by `g` with the composite of `θ K` of it with `H^i_Z(g)`,
which is zero. Since `θ K'` is an isomorphism, the class dies in `H⁰(RHom_A(K', ω⟦-i⟧)^∧)`. The
unit is natural, so that class is the image of `g ≫ u` under the unit at `K'`, and the unit is
injective on cohomology for a complex with finite cohomology modules; hence `g ≫ u = 0`. -/
theorem comp_eq_zero_of_homologyMap_localCohomology_eq_zero
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (hfin : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (op K', (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))))
    (hg : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g) = 0)
    (u : K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) :
    g ≫ u = 0 := by
  classical
  obtain ⟨θ, hθ⟩ := exists_localDualityExtNatEquiv A f hf ω hω ι hι i
  have hgz : ∀ y, ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g)).hom y = 0 := by
    intro y
    rw [hg]
    rfl
  -- the naturality square of local duality kills the image of the class of `u`
  have hθ' := hθ K K' g
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((DerivedCompletion.derivedCompletionUnit A f).app
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (op K,
            (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)))).hom
      (extHomologyZeroLinearEquiv A K
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) u))
  rw [show (θ K
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((DerivedCompletion.derivedCompletionUnit A f).app
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (op K,
              (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)))).hom
        (extHomologyZeroLinearEquiv A K
          ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) u))).comp
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g)).hom = 0 from
    LinearMap.ext fun y => by
      simp only [LinearMap.comp_apply, hgz, map_zero, LinearMap.zero_apply]] at hθ'
  have hzero := (θ K').injective (hθ'.trans (map_zero (θ K')).symm)
  -- the unit is natural, so the image is the class of `g ≫ u` at `K'`
  have hnat := (DerivedCompletion.derivedCompletionUnit A f).naturality
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
      (show (op K, (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) ⟶
          (op K', (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)
        from (g.op, 𝟙 ((CategoryTheory.shiftFunctor
          (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))))
  simp only [Functor.id_map] at hnat
  have key : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((DerivedCompletion.derivedCompletionUnit A f).app
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (op K',
            (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)))).hom
      (extHomologyZeroLinearEquiv A K'
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)
        (g ≫ u)) = 0 := by
    rw [extHomologyZeroLinearEquiv_naturality A g u, ← ModuleCat.comp_apply,
      ← Functor.map_comp, hnat, Functor.map_comp, ModuleCat.comp_apply]
    exact hzero
  -- and the unit is injective on cohomology
  have hker : extHomologyZeroLinearEquiv A K'
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)
      (g ≫ u) = 0 :=
    AdicCompletionCohomology.injective_homology_derivedCompletionUnit A f hf
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (op K', (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))
      hfin 0 (by rw [key, map_zero])
  exact (extHomologyZeroLinearEquiv A K'
    ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)).injective
    (hker.trans (map_zero _).symm)

/-- **The transport of the vanishing, with the finiteness side condition discharged.** The
hypothesis on the cohomology of `RHom_A(K', ω⟦-i⟧)` in
`Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero` holds whenever `K'`
is bounded above and `ω⟦-i⟧` bounded below, both with finite cohomology modules, by
`StacksDraft.DerivedHom.finite_homology_derivedHom`. That is the shape in which the hypothesis is
met in the proof of [Stacks, Tag 0EFX], where `K'` is a finite module in degree zero and `ω` is a
dualizing complex. -/
theorem comp_eq_zero_of_homologyMap_localCohomology_eq_zero_of_bounded
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K) (d b : ℤ)
    (hK'le : K'.IsLE d)
    (hωge : ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω).IsGE b)
    (hK'fin : ∀ k : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj K'))
    (hωfin : ∀ k : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)))
    (hg : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g) = 0)
    (u : K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) :
    g ≫ u = 0 :=
  comp_eq_zero_of_homologyMap_localCohomology_eq_zero A f hf ω hω ι hι i g
    (fun n => StacksDraft.DerivedHom.finite_homology_derivedHom
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)) K'
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) d b
      hK'le hωge hK'fin hωfin n) hg u

end Dualizing.LocalDuality

end
