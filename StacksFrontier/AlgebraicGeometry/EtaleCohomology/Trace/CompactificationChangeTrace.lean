module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFibreStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The trace formula does not depend on the compactification

Let `X` be a scheme over a finite field `k`, `Λ` a finite ring (possibly noncommutative) and
`g : j ⟶ l` a morphism of compactifications of `X` over `k`, with ambient proper morphism
`ḡ : X̄_j ⟶ X̄_l`. For a bounded below complex `K` on `X_étale` with perfect stalks, the trace
formula `T''(X̄_j, j_! K) = T'(X̄_j, j_! K)` implies `T''(X̄_l, l_! K) = T'(X̄_l, l_! K)`.

Indeed `l_! K ≅ ḡ_* j_! K` termwise (Tags 0F79 and 0F51, `Stacks.EtaleCohomology.refinementIso`);
the sheaves `j_! Kⁿ` are acyclic for the proper `ḡ_*`
(`Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_extensionByZero`, the vanishing
behind [Stacks, Tag 0F7G]), so `ḡ_*` of an injective resolution `j_! K ⟶ T` stays a
quasi-isomorphism; and the Leray step along `ḡ`
(`perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper`)
gives `T''(X̄_l, ḡ_* T) = T''(X̄_j, T)`. Both sides of `T'` are the sum over `X(k)` of the local
terms of `K`. This is the change of compactification in the proof of [Stacks, Tag 03V3], the
trace-formula form of [Stacks, Tag 0F7I], for an arbitrary finite coefficient ring.

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main results

* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_map_eq_of_rightAcyclic`:
  `T''` of `F(M)` and of `F(T)` agree for a quasi-isomorphism `M ⟶ T` of `F`-acyclic complexes.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_compactificationHom`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [Finite Λ] [IsAlgClosed kbar] [CharP kbar p] in
/-- **`T''` along a functor applied to a quasi-isomorphism of acyclic complexes.** Let `F` be an
additive functor from sheaves of `Λ`-modules on `Z` to sheaves on a scheme `Y` over `k` and
`ψ : M ⟶ T` a quasi-isomorphism of bounded below complexes of `F`-acyclic objects (for instance a
resolution by injectives of a complex of `F`-acyclic objects, or any quasi-isomorphism if `F` is
exact). Then `F(ψ)` is a quasi-isomorphism, so `RΓ(Y_k̄, -)` of `F(M)` is perfect
when that of `F(T)` is, with the same trace of the canonical geometric Frobenius. The functor is a
variable, so that the kernel never unfolds the étale functor it is instantiated with. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_map_eq_of_rightAcyclic
    {Z : Scheme.{u}} {Y : Over (Spec (.of k))} [EnoughInjectives (EtaleModules.{u, 0} Λ Z)]
    {F : EtaleModules.{u, 0} Λ Z ⥤ EtaleModules.{u, 0} Λ Y.left} [F.Additive]
    {M T : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z)} (ψ : M ⟶ T) (hψ : QuasiIso ψ.hom)
    (hT : ∀ n, F.rightAcyclic (T.obj.X n)) (hM : ∀ n, F.rightAcyclic (M.obj.X n))
    (hp : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar (F.mapCochainComplexPlus.obj T)))))) :
    ∃ hp' : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar (F.mapCochainComplexPlus.obj M))))),
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp'⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            (F.mapCochainComplexPlus.obj M))) =
        perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            (F.mapCochainComplexPlus.obj T))) := by
  have hq : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom) :=
    Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic F ψ.hom M.property T.property hM hT
  have hp' := isPerfect_frobeniusRestriction_of_quasiIso Λ kbar
    (C := F.mapCochainComplexPlus.obj M) (C' := F.mapCochainComplexPlus.obj T) _ hq hp
  obtain ⟨_, ht⟩ := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso Λ kbar p
    q hcard (C := F.mapCochainComplexPlus.obj M) (C' := F.mapCochainComplexPlus.obj T) _ hq hp'
  exact ⟨hp', ht⟩

section CompactificationHom

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {j l : CompactificationOf (Over.mk f)}

/-- **The trace formula does not depend on the compactification.** For a morphism `g : j ⟶ l` of
compactifications of `X` over `k` and a bounded below complex `K` on `X_étale` with perfect
stalks, `T''(X̄_j, j_! K) = T'(X̄_j, j_! K)` implies `T''(X̄_l, l_! K) = T'(X̄_l, l_! K)`: the
proof of [Stacks, Tag 0F7I], `l_! K ≅ ḡ_* j_! K` with `ḡ_*`-acyclic terms, followed by the Leray
step along the proper `ḡ`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_compactificationHom (g : j ⟶ l)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hK : HasPerfectStalks Λ K)
    (h : CohomologicalTraceFormula Λ kbar p q hcard (Over.mk j.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ j.immersion K hK)) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk l.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ l.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ l.immersion K hK) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ j.space
  let M := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K
  obtain ⟨hpM, htM⟩ := h
  obtain ⟨T, ψ, hψ, hT, -, -⟩ :=
    Functor.exists_twist_lift_of_injectiveResolution (𝟭 _) M (𝟙 _)
  have : ∀ n, Injective (T.obj.X n) := hT
  obtain ⟨hpT, htT⟩ := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso Λ kbar
    p q hcard (Y := Over.mk j.toBase) ψ.hom hψ hpM
  have hpπT := (isPerfect_frobeniusRestriction_directImage_iff_of_isProper Λ kbar
    (compactificationHomOver f g) T).2 hpT
  have hL := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper Λ kbar
    p q hcard (compactificationHomOver f g) T hpπT
  have hac (n : ℤ) : (etaleModuleDirectImage.{u, 0} Λ
      (compactificationHomOver f g).left).rightAcyclic (M.obj.X n) := by
    rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
    intro r hr
    exact isZero_rightDerived_etaleModuleDirectImage_extensionByZero Λ
      (CompactificationOf.immersion_comp_map g) (K.obj.X n) (isTorsionEtaleModule_of_finite Λ X _)
      r hr
  obtain ⟨hpπM, htπ⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_map_eq_of_rightAcyclic Λ kbar p q hcard
      (Y := Over.mk l.toBase)
      (F := etaleModuleDirectImage.{u, 0} Λ (compactificationHomOver f g).left) ψ hψ
      (fun n => Functor.rightAcyclic_of_injective _ _) hac hpπT
  let e : (etaleModuleExtensionByZero.{u, 0} Λ l.immersion).mapCochainComplexPlus.obj K ≅
      (etaleModuleDirectImage.{u, 0} Λ (compactificationHomOver f g).left).mapCochainComplexPlus.obj
        M :=
    ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex (refinementIso Λ g) _).app K.obj)
  let E := (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk l.toBase).hom (specAlgebraMap k kbar))).mapIso
      ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk l.toBase) kbar).mapIso e))
  have hpN := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso E) hpπM
  refine ⟨hpN, fun {_} => ?_⟩
  have he : perfectDerivedTrace.{0, u + 1} Λ ⟨_, hpN⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (Over.mk l.toBase) kbar p q hcard
          ((etaleModuleExtensionByZero.{u, 0} Λ l.immersion).mapCochainComplexPlus.obj K))) =
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hpπM⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (Over.mk l.toBase) kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ
            (compactificationHomOver f g).left).mapCochainComplexPlus.obj M))) := by
    refine perfectDerivedTrace_congr Λ ⟨_, hpN⟩ ⟨_, hpπM⟩ (DerivedCategory.Plus.ι.mapIso E) _ _ ?_
    rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Plus.ι.map
      (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk l.toBase) kbar p q hcard
        e.hom).symm
  have := finite_rationalPoints j.toBase
  have : Fintype (rationalPoints (Over.mk j.toBase).hom) :=
    Fintype.ofFinite (rationalPoints j.toBase)
  have : Fintype (rationalPoints f) := Fintype.ofInjective
    (rationalPointsMap (Over.mk l.toBase).hom l.immersion (Over.w l.obj.hom).symm)
    (fun a b h => Subtype.ext ((cancel_mono l.immersion).1 (congrArg Subtype.val h)))
  exact he.trans (htπ.trans (hL.trans (htT.symm.trans (htM.trans
    ((sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero Λ (f := f)
      (Y := Over.mk j.toBase) j.immersion (Over.w j.obj.hom) kbar p q hcard K hK
      (hasPerfectStalks_extensionByZero Λ j.immersion K hK)).trans
    (sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero Λ (f := f)
      (Y := Over.mk l.toBase) l.immersion (Over.w l.obj.hom) kbar p q hcard K hK
      (hasPerfectStalks_extensionByZero Λ l.immersion K hK)).symm)))))

end CompactificationHom

end Stacks.EtaleCohomology

end
