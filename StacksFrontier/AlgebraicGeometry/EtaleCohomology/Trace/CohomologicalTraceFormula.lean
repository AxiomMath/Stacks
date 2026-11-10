module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.Homology.Perfect.Filtration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# The trace formula `T'' = T'` on a scheme over a finite field, and its open/closed dévissage

Let `Y` be a scheme over a finite field `k`, `k̄` an algebraically closed extension of `k` and
`C` a bounded below complex of sheaves of `Λ`-modules on `Y_étale` whose stalks are perfect.
Following the notation of the proof of [Stacks, Tag 03UG], write

* `T''(Y, C) = Tr(π_Y^* | RΓ(Y_k̄, C|_{Y_k̄}))` for the trace of the canonical endomorphism
  `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo` (when `RΓ(Y_k̄, C|_{Y_k̄})` is
  perfect), and
* `T'(Y, C) = ∑_{y ∈ Y(k)} Tr(π_y | C_ȳ)`.

`Stacks.EtaleCohomology.CohomologicalTraceFormula` records that `RΓ(Y_k̄, C|_{Y_k̄})` is perfect
and `T''(Y, C) = T'(Y, C)`. For a compactification `j : X ⟶ X̄` and `C = j_! K` this is the
trace formula of Tag 03UG for `K` on `X`, since `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` by
definition.

The results of this file are the formal parts of the dévissage of Tag 03UG:

* the statement only depends on `C` up to isomorphism;
* it holds for a complex all of whose terms vanish, and on a finite étale `k`-scheme (Step 2);
* **Step 1**: for a closed immersion `i : Z ⟶ Y` with open complement `j : U ⟶ Y`, it holds for
  `C` as soon as it holds for `j_! j^{-1} C` on `Y` and for `i^{-1} C` on `Z`;
* consequently it holds when `C` restricts to zero off a finite étale closed subscheme.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `frobeniusRestrictionCohomologyEndo`)
are defined there.

## Main definitions

* `Stacks.EtaleCohomology.HasPerfectStalks`: the stalks of `C` at all geometric points are
  perfect.
* `Stacks.EtaleCohomology.CohomologicalTraceFormula`: `RΓ(Y_k̄, C|_{Y_k̄})` is perfect and
  `T''(Y, C) = T'(Y, C)`.

## Main results

* `Stacks.EtaleCohomology.cohomologicalTraceFormula_of_openClosed`: Step 1 of Tag 03UG.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_of_etale`: Step 2 of Tag 03UG.
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_of_isZero_restriction`: the trace formula for
  a complex vanishing off a finite étale closed subscheme.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 and 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe w u

namespace Stacks.EtaleCohomology

section Stalks

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ]

/-- The stalks `C_s̄` of a bounded below complex of sheaves of `Λ`-modules at all geometric points
`s̄` are perfect complexes of `Λ`-modules. -/
abbrev HasPerfectStalks [HasDerivedCategory.{w} (ModuleCat.{u + 1} Λ)] {X : Scheme.{u}}
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) : Prop :=
  ∀ s : GeometricPoint X, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
    (((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C.obj))

/-- Perfectness of the stalks only depends on the complex up to a degreewise isomorphism. -/
theorem hasPerfectStalks_of_iso [HasDerivedCategory.{w} (ModuleCat.{u + 1} Λ)] {X : Scheme.{u}}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (e : ∀ n, C.obj.X n ≅ C'.obj.X n)
    (he : ∀ a b, C.obj.d a b ≫ (e b).hom = (e a).hom ≫ C'.obj.d a b)
    (hC : HasPerfectStalks.{w} Λ C) : HasPerfectStalks.{w} Λ C' := fun s =>
  StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => ((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).mapIso (e n))
      (fun a b _ => by
        have h := congrArg ((Scheme.pointSmallEtale s.hom).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map (he a b)
        rw [Functor.map_comp, Functor.map_comp] at h
        exact h.symm))).symm (hC s)

end Stalks

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ]

/-- **Stalks of an extension by zero are perfect** when those of the complex are: the stalk of
`j_! K` at a geometric point is the stalk of `K` at a lift of the point through `j`, or zero when
there is no lift. -/
theorem hasPerfectStalks_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) (hK : HasPerfectStalks Λ K) :
    HasPerfectStalks Λ ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj K) := by
  intro s
  by_cases hs : s.hom.base default ∈ Set.range j.base
  · obtain ⟨t, ht⟩ := hs
    obtain ⟨s', hs'⟩ := exists_lift_of_isPreimmersion j s.hom t ht
    let E : etaleModuleExtensionByZero.{u, 0} Λ j ⋙
          (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
        (Scheme.pointSmallEtale s').sheafFiber (A := ModuleCat.{u + 1} Λ) :=
      eqToIso (by rw [← hs']) ≪≫
        Functor.isoWhiskerLeft _ (etaleModuleStalkPullbackIso.{u, 0} Λ j s').symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (extensionByZeroInverseImageIso.{u, 0} Λ j) _ ≪≫
        Functor.leftUnitor _
    let e : (((Scheme.pointSmallEtale s.hom).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj K).obj ≅
        (((Scheme.pointSmallEtale s').sheafFiber
          (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj :=
      HomologicalComplex.Hom.isoOfComponents (fun n => E.app (K.obj.X n))
        (fun a b _ => (E.hom.naturality (K.obj.d a b)).symm)
    exact StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso e)
      (hK ⟨s.residueField, s'⟩)
  · refine StacksDraft.Perfect.isPerfect_of_isZero _ (Functor.map_isZero _ ?_)
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    refine IsZero.eq_of_src ?_ _ _
    change IsZero (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j).obj (K.obj.X n)))
    have hd : Disjoint (Set.range s.hom.base) (Set.range j.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨t, rfl⟩
      have : t = default := Subsingleton.elim _ _
      exact this ▸ hs
    have h1 : IsZero (((Scheme.pointSmallEtale (𝟙 _ ≫ s.hom)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j).obj (K.obj.X n))) :=
      IsZero.of_iso (Functor.map_isZero ((Scheme.pointSmallEtale (𝟙 _)).sheafFiber
          (A := ModuleCat.{u + 1} Λ))
          (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ s.hom j hd _))
        ((etaleModuleStalkPullbackIso.{u, 0} Λ s.hom (𝟙 _)).app _).symm
    rw [Category.id_comp] at h1
    exact h1

/-- Stalks of the restriction `j^{-1} C` along an open immersion are perfect when those of `C`
are. -/
theorem hasPerfectStalks_restriction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hC : HasPerfectStalks Λ C) :
    HasPerfectStalks Λ ((etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj C) :=
  hasPerfectStalks_of_iso Λ
    (C := (etaleModuleInverseImage.{u, 0} Λ j).mapCochainComplexPlus.obj C)
    (fun n => (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app (C.obj.X n))
    (fun a b => (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).hom.naturality (C.obj.d a b))
    (isPerfect_stalk_inverseImage Λ j C hC)

/-- Stalks of `j_! j^{-1} C` are perfect when those of `C` are. -/
theorem hasPerfectStalks_extensionByZero_restriction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hC : HasPerfectStalks Λ C) :
    HasPerfectStalks Λ ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj
      ((etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj C)) :=
  hasPerfectStalks_extensionByZero Λ j _ (hasPerfectStalks_restriction Λ j C hC)

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **The trace formula `T''(Y, C) = T'(Y, C)` of [Stacks, Tag 03UG]** for a bounded below
complex `C` with perfect stalks on a scheme `Y` over the finite field `k`: `RΓ(Y_k̄, C|_{Y_k̄})`
is perfect, and the trace of the canonical geometric Frobenius on it is the sum over the rational
points `y ∈ Y(k)` of the traces of `π_y` on the stalks `C_ȳ`. -/
def CohomologicalTraceFormula (Y : Over (Spec (.of k)))
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) (hC : HasPerfectStalks Λ C) : Prop :=
  ∃ hp : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C)))),
    ∀ [Fintype (rationalPoints Y.hom)],
      perfectDerivedTrace Λ ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard C)) =
        ∑ y : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hC (rationalGeometricPoint kbar y.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y.1 C))

/-- **The trace formula only depends on the complex up to isomorphism.** -/
theorem cohomologicalTraceFormula_of_iso {Y : Over (Spec (.of k))}
    {C C' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (e : C ≅ C')
    (hC : HasPerfectStalks Λ C) (hC' : HasPerfectStalks Λ C')
    (h : CohomologicalTraceFormula Λ kbar p q hcard Y C hC) :
    CohomologicalTraceFormula Λ kbar p q hcard Y C' hC' := by
  obtain ⟨hp, ht⟩ := h
  let E := (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
      ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).mapIso e))
  have hp' := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso E).symm hp
  refine ⟨hp', fun {_} => ?_⟩
  refine (perfectDerivedTrace_congr Λ ⟨_, hp⟩ ⟨_, hp'⟩ (DerivedCategory.Plus.ι.mapIso E) _ _
      ?_).symm.trans
    (ht.trans ?_)
  · rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Plus.ι.map
      (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar p q hcard e.hom).symm
  let e' : ∀ n, C.obj.X n ≅ C'.obj.X n := fun n =>
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso ((ObjectProperty.ι _).mapIso e)
  refine Fintype.sum_congr _ _ fun y => ?_
  exact perfectDerivedTrace_rationalPointStalkFrobenius_congr Λ kbar p q hcard y.1 e'
    (fun a b => (e.hom.hom.comm a b).symm) _ _

/-- **Step 2 of [Stacks, Tag 03UG]: the trace formula on a finite étale `k`-scheme.** -/
theorem cohomologicalTraceFormula_of_etale (Y : Over (Spec (.of k))) [Etale Y.hom]
    [IsFinite Y.hom] (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left))
    (hC : HasPerfectStalks Λ C) : CohomologicalTraceFormula Λ kbar p q hcard Y C hC :=
  ⟨isPerfect_frobeniusRestriction_of_etale Λ Y kbar C hC, fun {_} =>
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale' Λ Y kbar p q hcard C
      _ hC⟩

/-- The rational points of a closed subscheme are finite when those of the ambient scheme are. -/
abbrev rationalPointsFintypeOfMono {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) [Mono i.left]
    [Fintype (rationalPoints Y.hom)] : Fintype (rationalPoints Z.hom) :=
  Fintype.ofInjective (rationalPointsMap Y.hom i.left (Over.w i).symm)
    (fun _ _ h => Subtype.ext ((cancel_mono i.left).1 (congrArg Subtype.val h)))

/-- Rational points of a monomorphic `W ⟶ X` over `k` inject into those of `X`. -/
private theorem rationalPointsMap_injective_of_mono {k : Type u} [Field k] {W X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : W ⟶ X) [Mono g] {fW : W ⟶ Spec (.of k)} (h : fW = g ≫ f) :
    Function.Injective (rationalPointsMap f g h) :=
  fun _ _ h => Subtype.ext ((cancel_mono g).1 (congrArg Subtype.val h))

/-- **Step 1 of [Stacks, Tag 03UG]: the open and closed dévissage of the trace formula.** For a
closed immersion `i : Z ⟶ Y` with open complement `j : U ⟶ Y`, the trace formula holds for `C` on
`Y` as soon as it holds for `j_! j^{-1} C` on `Y` and for `i^{-1} C` on `Z`. -/
theorem cohomologicalTraceFormula_of_openClosed {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y)
    [IsClosedImmersion i.left] {U : Scheme.{u}} (j : U ⟶ Y.left) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.left.base)ᶜ)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) (hC : HasPerfectStalks Λ C)
    (h₁ : CohomologicalTraceFormula Λ kbar p q hcard Y
      ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj
        ((etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj C))
      (hasPerfectStalks_extensionByZero_restriction Λ j C hC))
    (h₃ : CohomologicalTraceFormula Λ kbar p q hcard Z
      ((etaleModuleInverseImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj C)
      (isPerfect_stalk_inverseImage Λ i.left C hC)) :
    CohomologicalTraceFormula Λ kbar p q hcard Y C hC := by
  obtain ⟨hp₁, ht₁⟩ := h₁
  obtain ⟨hpZ, ht₃⟩ := h₃
  have hp₃ := (isPerfect_frobeniusRestriction_directImage_iff Λ i kbar _).2 hpZ
  have hS := openClosedCochainShortComplex_shortExact Λ i.left j hij C.obj
  have hp₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar C)))) :=
    Functor.isPerfect_twistDerivedObj_X₂.{0, u + 1}
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
      (fieldBaseChangeRestriction_shortExact.{u, 0} Λ Y kbar hS)
      (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj
          ((etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj C))).property)
      (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        C).property)
      (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj C))).property)
      hp₁ hp₃
  refine ⟨hp₂, fun {_} => ?_⟩
  have := rationalPointsFintypeOfMono i
  have : Finite (rationalPoints (j ≫ Y.hom)) := Finite.of_injective
    _ (rationalPointsMap_injective_of_mono Y.hom j rfl)
  rw [perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_add_openClosed Λ Y i.left j hij
      kbar p q hcard C hp₁ hp₂ hp₃,
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage Λ i p q hcard kbar _ hp₃ hpZ,
    ht₁, ht₃, sum_perfectDerivedTrace_rationalPointStalkFrobenius_eq_add Λ i j hij kbar p q hcard C
      hC (hasPerfectStalks_extensionByZero_restriction Λ j C hC)]

/-- **The trace formula is invariant under closed immersions**: for a closed immersion
`i : Z ⟶ Y` over `k`, if `T''(Z, G) = T'(Z, G)` then `T''(Y, i_* G) = T'(Y, i_* G)`. -/
theorem cohomologicalTraceFormula_directImage {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y)
    [IsClosedImmersion i.left] (G : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    (hG : HasPerfectStalks Λ G)
    (hiG : HasPerfectStalks Λ
      ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj G))
    (h : CohomologicalTraceFormula Λ kbar p q hcard Z G hG) :
    CohomologicalTraceFormula Λ kbar p q hcard Y
      ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj G) hiG := by
  obtain ⟨hpZ, ht⟩ := h
  have hp := (isPerfect_frobeniusRestriction_directImage_iff Λ i kbar G).2 hpZ
  refine ⟨hp, fun {_} => ?_⟩
  have := rationalPointsFintypeOfMono i
  rw [perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage Λ i p q hcard kbar _ hp
      hpZ,
    ht]
  refine Fintype.sum_of_injective _
    (rationalPointsMap_injective_of_mono Y.hom i.left (Over.w i).symm) _ _ ?_ ?_
  · intro y hy
    refine perfectDerivedTrace_eq_zero_of_isZero Λ _ ?_ _
    refine Functor.map_isZero DerivedCategory.Q
      (isZero_rationalPointStalkComplex_directImage Λ i.left kbar y.1 ?_ G)
    rintro ⟨t, ht⟩
    obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion i.left y.1 t ht
    exact hy ⟨⟨g, by rw [← Over.w i, ← Category.assoc, hg]; exact y.2⟩, Subtype.ext hg⟩
  · intro z
    exact (perfectDerivedTrace_rationalPointStalkFrobenius_directImage Λ i.left kbar z.1 _ rfl
      p q hcard G _ _).symm

/-- **The trace formula for a complex supported on a finite étale closed subscheme**: if `C`
restricts to zero on the open complement of a closed immersion `i : Z ⟶ Y` with `Z` finite étale
over `k`, then `T''(Y, C) = T'(Y, C)`. Indeed `C ≅ i_* i^{-1} C`, and Step 2 applies on `Z`. -/
theorem cohomologicalTraceFormula_of_isZero_restriction {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y)
    [IsClosedImmersion i.left] [Etale Z.hom] [IsFinite Z.hom] {U : Scheme.{u}} (j : U ⟶ Y.left)
    [IsOpenImmersion j] (hij : Set.range j.base = (Set.range i.left.base)ᶜ)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) (hC : HasPerfectStalks Λ C)
    (hz : ∀ n, IsZero ((etaleModuleRestriction.{u, 0} Λ j).obj (C.obj.X n))) :
    CohomologicalTraceFormula Λ kbar p q hcard Y C hC := by
  let e : C ≅ (etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj C) :=
    ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
      (fun n => @asIso _ _ _ _ ((etaleModuleInverseImageAdj.{u, 0} Λ i.left).unit.app (C.obj.X n))
        (isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ i.left j hij _ (hz n)))
      (fun a b _ => ((etaleModuleInverseImageAdj.{u, 0} Λ i.left).unit.naturality
        (C.obj.d a b)).symm))
  have hiC : HasPerfectStalks Λ ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj C)) :=
    hasPerfectStalks_of_iso Λ (fun n => (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      ((ObjectProperty.ι _).mapIso e)) (fun a b => (e.hom.hom.comm a b).symm) hC
  exact cohomologicalTraceFormula_of_iso Λ kbar p q hcard e.symm hiC hC
    (cohomologicalTraceFormula_directImage Λ kbar p q hcard i _
      (isPerfect_stalk_inverseImage Λ i.left C hC) hiC
      (cohomologicalTraceFormula_of_etale Λ kbar p q hcard Z _ _))

end Standard

end Stacks.EtaleCohomology

end
