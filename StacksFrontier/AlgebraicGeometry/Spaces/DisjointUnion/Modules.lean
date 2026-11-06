module

public import StacksFrontier.CategoryTheory.Adjunction.PiProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Covering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Modules on a disjoint union of algebraic spaces

Let `Z` be the disjoint union of a family `X i` of algebraic spaces over `S`, with injections
`j i : X i ⟶ Z`. Restriction to the summands identifies `𝒪_Z`-modules with families of
`𝒪_{X i}`-modules: the functor `Mod(𝒪_Z) ⥤ ∏ i, Mod(𝒪_{X i})`, `M ↦ (M|_{X i})_i`, is an
equivalence, with quasi-inverse `(N i)_i ↦ ∏ i, (j i)_* N i`.

## Main results

* `AlgebraicGeometry.Space.isZero_modules_of_forall_isEmpty`: every module on an algebraic
  space all of whose étale charts are empty is zero.
* `AlgebraicGeometry.Space.isEmpty_of_comp_eq_of_ne`: an algebraic space mapping to two
  distinct summands compatibly has only empty charts.
* `AlgebraicGeometry.Space.isZero_etaleModulePullback_modulePushforward_of_ne`: the direct
  image from one summand restricts to zero on another.
* `AlgebraicGeometry.Space.isEquivalence_pi'_etaleModulePullback_of_isColimit`: the
  restrictions to the summands identify `Mod(𝒪_Z)` with `∏ i, Mod(𝒪_{X i})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every module on an algebraic space all of whose étale charts have empty underlying scheme is
zero. -/
theorem isZero_modules_of_forall_isEmpty {T : AlgebraicSpaces B S hS}
    (h : ∀ V : SmallEtale B S hS T.1,
      IsEmpty ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T.1).obj V)))
    (M : Modules.{u, u} B S hS T.1 T.2) : IsZero M := by
  have hM : Presieve.IsSheaf (SmallEtale.topology B S hS T.1)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ M.isSheaf)
  have hsub : ∀ (V : SmallEtale B S hS T.1) (x y : M.val.obj (op V)), x = y := by
    intro V x y
    have hbot : (⊥ : Sieve V) ∈ SmallEtale.topology B S hS T.1 V :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS T.1 ⊥).2 fun z => (h V).elim z
    exact (hM.isSeparated _ hbot).ext fun _ _ hf => hf.elim
  refine (IsZero.iff_id_eq_zero M).2
    (SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_))
  ext x
  exact hsub V.unop _ _

variable {ι : Type u} {X : ι → AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS}
  {j : ∀ i, X i ⟶ Z}

/-- An algebraic space with compatible morphisms to two distinct summands of a disjoint union
has only empty étale charts. -/
theorem isEmpty_of_comp_eq_of_ne
    (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
      fun i => (algebraicSpacesToSheaf B S hS).map (j i)))
    {k i : ι} (hki : k ≠ i) {T : AlgebraicSpaces B S hS} (a : T ⟶ X k) (b : T ⟶ X i)
    (w : a ≫ j k = b ≫ j i) (V : SmallEtale B S hS T.1) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T.1).obj V)) := by
  let v : T.1.obj (op V.1.left) := yonedaEquiv V.1.hom
  refine Sheaf.isEmpty_toScheme_of_eq_of_ne _ hc hki (a.hom.app _ v) (b.hom.app _ v) ?_
  exact congrArg (fun φ : T ⟶ Z => φ.hom.app (op V.1.left) v) w

section Equivalence

variable (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
  fun i => (algebraicSpacesToSheaf B S hS).map (j i)))

/-- The restriction to the summand `k` of the direct image from another summand `i ≠ k` is
zero. -/
theorem isZero_etaleModulePullback_modulePushforward_of_ne {k i : ι} (hki : k ≠ i)
    (N : Modules.{u, u} B S hS (X i).1 (X i).2) :
    IsZero ((etaleModulePullback.{u, u} B S hS (j k) (isEtale_cofanInj_of_isColimit hc k)).obj
      ((modulePushforward B S hS (j i)).obj N)) := by
  have sq := IsPullback.of_hasPullback (j i) (j k)
  have e := (modulePushforwardEtaleBaseChangeIso B S hS (pullback.fst (j i) (j k))
    (pullback.snd (j i) (j k)) (j i) (j k) sq (isEtale_cofanInj_of_isColimit hc k)).app N
  have := (modulePullbackAdjunction B S hS (pullback.snd (j i) (j k))).isRightAdjoint
  refine IsZero.of_iso ?_ e.symm
  exact Functor.map_isZero (modulePushforward B S hS (pullback.snd (j i) (j k)))
    (isZero_modules_of_forall_isEmpty
      (isEmpty_of_comp_eq_of_ne hc hki _ _ pullback.condition.symm) _)

/-- Restriction to the summands of a disjoint union is faithful. -/
theorem eq_of_forall_etaleModulePullback_map_eq {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (φ ψ : M ⟶ N) (h : ∀ i,
      (etaleModulePullback.{u, u} B S hS (j i) (isEtale_cofanInj_of_isColimit hc i)).map φ =
        (etaleModulePullback.{u, u} B S hS (j i) (isEtale_cofanInj_of_isColimit hc i)).map ψ) :
    φ = ψ := by
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS X j
    (isEtaleCovering_cofanInj_of_isColimit hc) φ ψ fun i => ?_
  let e := modulePullbackIsoEtaleModulePullback B S hS (j i) (isEtale_cofanInj_of_isColimit hc i)
  exact (Iso.cancel_iso_hom_right _ _ (e.app N)).1 ((e.hom.naturality φ).trans
    ((congrArg (e.hom.app M ≫ ·) (h i)).trans (e.hom.naturality ψ).symm))

/-- Restriction to all the summands of a disjoint union, as a functor to the product, is
faithful. -/
theorem faithful_pi'_etaleModulePullback :
    (Functor.pi' fun i =>
      etaleModulePullback.{u, u} B S hS (j i) (isEtale_cofanInj_of_isColimit hc i)).Faithful :=
  ⟨fun {_ _} φ ψ h => eq_of_forall_etaleModulePullback_map_eq hc φ ψ fun i => congrFun h i⟩

/-- The counit `j i^* (j i)_* ⟶ 𝟭` is invertible for the injection of a summand, an open
immersion. -/
theorem isIso_etaleModulePullbackAdjunction_counit_of_isColimit_cofan (i : ι)
    (N : Modules.{u, u} B S hS (X i).1 (X i).2) :
    IsIso ((etaleModulePullbackAdjunction B S hS (j i)
      (isEtale_cofanInj_of_isColimit hc i)).counit.app N) :=
  isIso_etaleModulePullbackAdjunction_counit B S hS (j i)
    (isOpenImmersion_cofanInj_of_isColimit hc i) N

/-- **Modules on a disjoint union.** Restriction to the summands identifies `𝒪_Z`-modules on a
disjoint union `Z = ⨆ i, X i` of algebraic spaces with families of `𝒪_{X i}`-modules. -/
theorem isEquivalence_pi'_etaleModulePullback_of_isColimit :
    (Functor.pi' fun i =>
      etaleModulePullback.{u, u} B S hS (j i) (isEtale_cofanInj_of_isColimit hc i)).IsEquivalence :=
  have := faithful_pi'_etaleModulePullback hc
  Adjunction.isEquivalence_pi'_of_isZero
    (fun i => etaleModulePullbackAdjunction B S hS (j i) (isEtale_cofanInj_of_isColimit hc i))
    (isIso_etaleModulePullbackAdjunction_counit_of_isColimit_cofan hc)
    (fun _ _ hki N => isZero_etaleModulePullback_modulePushforward_of_ne hc hki N)

end Equivalence

end AlgebraicGeometry.Space

end
