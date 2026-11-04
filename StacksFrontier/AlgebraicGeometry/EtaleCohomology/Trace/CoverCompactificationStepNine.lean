module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactificationBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapOpenClosedConstantComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusFixedPoints

/-!
# Step 9 on the compactification of a Galois cover

Let `j : V ⟶ V̄` be the smooth projective compactification of a connected finite étale cover
`f : V ⟶ U` of a smooth curve over a finite field `k` with `U(k) = ∅`
(`AlgebraicGeometry.CoverCompactification`), `a` an automorphism of `V` over `U` and `σ_a` its
extension to `V̄`. For a bounded below complex of modules `N`, the twisted Frobenius
`(σ̄_a π̄)^*` on `RΓ(V̄_k̄, (j_! j^{-1} N_{V̄})|_{V̄_k̄})` has trace zero, granted Weil's formula
on `V̄_k̄`: this is Step 9 of the proof of [Stacks, Tag 03UG] with all geometric hypotheses of
`Stacks.EtaleCohomology.perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_zero`
discharged (the boundary `W = V̄ ∖ V` is finite étale over `k`, `V_k̄` and `W_k̄` are stable under
`σ̄_a π̄`, and `σ̄_a π̄` has no fixed point on `V_k̄` because `U` has no rational point).

## Main results

* `Stacks.EtaleCohomology.isOpenImmersion_fieldBaseChangeMap`.
* `Stacks.EtaleCohomology.twistedGeometricFrobenius_comp_fieldBaseChangeMap_of_comm`.
* `Stacks.EtaleCohomology.perfectDerivedTrace_twistedFrobenius_coverCompactification_eq_zero`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace AlgebraicGeometry.CoverCompactification

variable {k : Type u} [Field k] [PerfectField k] {U Ub V : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb] {jU : U ⟶ Ub}
  [IsOpenImmersion jU] (hjU : jU ≫ pUb = pU) {f : V ⟶ U} [IsFinite f] [Etale f]
  [ConnectedSpace V] (C : CoverCompactification k pUb jU f)

/-- `V̄` as a `k`-scheme. -/
abbrev toOver : Over (Spec (.of k)) := Over.mk C.q

/-- `V` as a `k`-scheme through `V̄`. -/
abbrev openOver : Over (Spec (.of k)) := Over.mk (C.j ≫ C.q)

/-- The boundary `W` as a `k`-scheme. -/
abbrev boundaryOver : Over (Spec (.of k)) := Over.mk (C.boundaryι ≫ C.q)

/-- `j : V ⟶ V̄` over `k`. -/
abbrev openOverHom : C.openOver ⟶ C.toOver := Over.homMk C.j

/-- `W ⟶ V̄` over `k`. -/
abbrev boundaryOverHom : C.boundaryOver ⟶ C.toOver := Over.homMk C.boundaryι

/-- The extension `σ_a` of an automorphism `a` of `V` over `U`, over `k`. -/
abbrev extendOver (a : V ≅ V) (ha : a.hom ≫ f = f) : C.toOver ⟶ C.toOver :=
  Over.homMk (C.extend pU hjU a.hom ha) (C.extend_comp_q pU hjU a.hom ha)

/-- An automorphism `a` of `V` over `U`, over `k`. -/
abbrev openOverAut (a : V ≅ V) (ha : a.hom ≫ f = f) : C.openOver ⟶ C.openOver :=
  Over.homMk a.hom (by
    change a.hom ≫ C.j ≫ C.q = C.j ≫ C.q
    rw [C.j_comp_q pU hjU, reassoc_of% ha])

/-- The restriction of `σ_a` to the boundary, over `k`. -/
abbrev boundaryOverAut (a : V ≅ V) (ha : a.hom ≫ f = f) : C.boundaryOver ⟶ C.boundaryOver :=
  Over.homMk (C.boundaryExtend hjU a ha) (by
    change C.boundaryExtend hjU a ha ≫ C.boundaryι ≫ C.q = C.boundaryι ≫ C.q
    rw [boundaryExtend_comp_ι_assoc, extend_comp_q])

/-- The structure morphism of `V` over `k` factors through `U`. -/
abbrev openOverToBase : C.openOver ⟶ Over.mk pU :=
  Over.homMk f (C.j_comp_q pU hjU).symm

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsOpenImmersion jU] [IsFinite f] [Etale f] in
/-- Over `k`, the open immersion `j : V ⟶ V̄` intertwines `a` with its extension `σ_a`. -/
lemma openOverAut_comp_openOverHom (a : V ≅ V) (ha : a.hom ≫ f = f) :
    C.openOverAut hjU a ha ≫ C.openOverHom = C.openOverHom ≫ C.extendOver hjU a ha := by
  ext1
  exact (C.j_comp_extend pU hjU a.hom ha).symm

omit [IsCurve k pU] [Smooth pU] in
/-- Over `k`, the inclusion `W ⟶ V̄` intertwines the restriction of `σ_a` to `W` with `σ_a`. -/
lemma boundaryOverAut_comp_boundaryOverHom (a : V ≅ V) (ha : a.hom ≫ f = f) :
    C.boundaryOverAut hjU a ha ≫ C.boundaryOverHom = C.boundaryOverHom ≫ C.extendOver hjU a ha := by
  ext1
  exact C.boundaryExtend_comp_ι hjU a ha

omit [PerfectField k] [IsCurve k pU] [Smooth pU] [IsProper pUb] [IsOpenImmersion jU] [IsFinite f]
  [Etale f] [ConnectedSpace V] in
/-- Over `k`, the automorphism `a` of `V` followed by `f : V ⟶ U` is `f`. -/
lemma openOverAut_comp_openOverToBase (a : V ≅ V) (ha : a.hom ≫ f = f) :
    C.openOverAut hjU a ha ≫ C.openOverToBase hjU = C.openOverToBase hjU := by
  ext1
  exact ha

/-- The extension `σ_a : V̄ ⟶ V̄` of an automorphism `a` of `V` over `U` is an isomorphism. -/
instance (a : V ≅ V) (ha : a.hom ≫ f = f) : IsIso (C.extendOver hjU a ha).left :=
  inferInstanceAs (IsIso (C.extendIso pU hjU a ha).hom)

end AlgebraicGeometry.CoverCompactification

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))} (i : Z ⟶ Y) (kbar : Type u)
  [Field kbar] [Algebra k kbar]

/-- The base change to `k̄` of an open immersion over `k` is an open immersion. -/
lemma isOpenImmersion_fieldBaseChangeMap [IsOpenImmersion i.left] :
    IsOpenImmersion (fieldBaseChangeMap i kbar) :=
  have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion i.left))
    (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w i).symm (Category.id_comp _).symm

/-- Base change to `k̄` is functorial. -/
lemma fieldBaseChangeMap_comp {X : Over (Spec (.of k))} (i' : Y ⟶ X) :
    fieldBaseChangeMap (i ≫ i') kbar = fieldBaseChangeMap i kbar ≫ fieldBaseChangeMap i' kbar := by
  refine pullback.hom_ext ?_ ?_
  · rw [fieldBaseChangeMap_comp_fst, Category.assoc, fieldBaseChangeMap_comp_fst,
      reassoc_of% (fieldBaseChangeMap_comp_fst i kbar), Over.comp_left]
  · rw [fieldBaseChangeMap_comp_snd, Category.assoc, fieldBaseChangeMap_comp_snd,
      fieldBaseChangeMap_comp_snd]

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`i_k̄` intertwines the twisted Frobenii** of `σ_Z` and `σ_Y` when `σ_Z ≫ i = i ≫ σ_Y`. -/
lemma twistedGeometricFrobenius_comp_fieldBaseChangeMap_of_comm (σZ : Z ⟶ Z) (σY : Y ⟶ Y)
    (h : σZ ≫ i = i ≫ σY) :
    twistedGeometricFrobenius Z σZ kbar p q hcard ≫ fieldBaseChangeMap i kbar =
      fieldBaseChangeMap i kbar ≫ twistedGeometricFrobenius Y σY kbar p q hcard := by
  rw [Category.assoc, geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar,
    ← Category.assoc, ← fieldBaseChangeMap_comp, h, fieldBaseChangeMap_comp, Category.assoc]

end BaseChange

section Cover

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U Ub V : Scheme.{u}}
  {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb]
  {jU : U ⟶ Ub} [IsOpenImmersion jU] (hjU : jU ≫ pUb = pU) {f : V ⟶ U} [IsFinite f] [Etale f]
  [ConnectedSpace V] (C : CoverCompactification k pUb jU f) (a : V ≅ V) (ha : a.hom ≫ f = f)
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q) (Λ : Type) [CommRing Λ]
  (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ))

omit [IsCurve k pU] [Smooth pU] in
include hjU in
/-- **Step 9 of [Stacks, Tag 03UG] on the compactification of a Galois cover.**  Let
`f : V ⟶ U` be a connected finite étale cover of a smooth curve over the finite field `k` with
`U(k) = ∅`, `V̄` its smooth projective compactification and `σ_a` the extension to `V̄` of an
automorphism `a` of `V` over `U`. Granted Weil's formula `Tr(φ^* | RΓ(V̄_k̄, N)) = #Fix(φ) ·
Tr(id | Γ(k̄, N))` for `φ = σ̄_a π̄`, the twisted Frobenius `(σ̄_a π̄)^*` on
`RΓ(V̄_k̄, (j_! j^{-1} N_{V̄})|_{V̄_k̄})` has trace zero. -/
theorem perfectDerivedTrace_twistedFrobenius_coverCompactification_eq_zero
    [IsEmpty (rationalPoints pU)]
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ C.toOver C.j N)))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar)) (etaleModuleConstantComplex Λ kbar N))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} Λ
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex Λ kbar N))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex Λ (etaleModuleConstantComplex Λ kbar N).obj)))
    (hweil : perfectDerivedTrace Λ ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, 0} Λ
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)
          (twistedGeometricFrobenius_comp_toBase C.toOver (C.extendOver hjU a ha) kbar p q hcard)
          (etaleModuleConstantComplex Λ kbar N))) =
      Nat.card (fixedSections (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)) •
          perfectDerivedTrace Λ ⟨_, hΓ⟩ (𝟙 _)) :
    perfectDerivedTrace Λ ⟨_, hZ⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} Λ
          (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (pullback.snd C.toOver.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ
          (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard)
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
          (twistedGeometricFrobenius_comp_toBase C.toOver (C.extendOver hjU a ha) kbar p q
            hcard).symm)
        ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
          (extensionByZeroConstantComplex Λ C.toOver C.j N))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ C.toOver C.j N))
          (Y := (etaleModuleDirectImage.{u, 0} Λ
            (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q
              hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex Λ C.toOver C.j N)))
          (Functor.twistedBaseChangeTwistHC
            (etaleModuleDirectImage.{u, 0} Λ
              (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard))
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj C.toOver kbar))
            (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange C.toOver kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap (C.extendOver hjU a ha) kbar))
            (etaleModuleDirectImage.{u, 0} Λ (C.extendOver hjU a ha).left)
            (frobeniusBaseChangeTwist.{u, 0} Λ C.toOver kbar p q hcard)
            (automorphismBaseChange Λ C.toOver (C.extendOver hjU a ha) kbar)
            (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap (C.extendOver hjU a ha) kbar)
              (geometricFrobeniusBaseChange C.toOver kbar p q hcard)
              (twistedGeometricFrobenius C.toOver (C.extendOver hjU a ha) kbar p q hcard) rfl)
            (extensionByZeroConstantComplex Λ C.toOver C.j N).obj
            (extensionByZeroConstantTwist Λ C.toOver (C.extendOver hjU a ha) C.j a.hom
              (C.isPullback_extend pU hjU a ha) N)
            (extensionByZeroConstantTwist_comm Λ C.toOver (C.extendOver hjU a ha) C.j a.hom
              (C.isPullback_extend pU hjU a ha) N))))) = 0 := by
  have : IsOpenImmersion C.openOverHom.left := inferInstanceAs (IsOpenImmersion C.j)
  have : IsClosedImmersion C.boundaryOverHom.left :=
    inferInstanceAs (IsClosedImmersion C.boundaryι)
  have := isOpenImmersion_fieldBaseChangeMap C.openOverHom kbar
  have := isClosedImmersion_fieldBaseChangeMap C.boundaryOverHom kbar
  have : IsEmpty (rationalPoints (Over.mk pU).hom) := ‹IsEmpty (rationalPoints pU)›
  have : Etale C.boundaryOver.hom := inferInstanceAs (Etale (C.boundaryι ≫ C.q))
  have : IsFinite C.boundaryOver.hom := inferInstanceAs (IsFinite (C.boundaryι ≫ C.q))
  have hij' : Set.range (fieldBaseChangeMap C.openOverHom kbar).base =
      (Set.range (fieldBaseChangeMap C.boundaryOverHom kbar).base)ᶜ := by
    have h1 := range_fieldBaseChangeMap C.openOverHom kbar
    have h2 := range_fieldBaseChangeMap C.boundaryOverHom kbar
    show Set.range (fieldBaseChangeMap C.openOverHom kbar) = _
    rw [h1, show Set.range (fieldBaseChangeMap C.boundaryOverHom kbar).base =
      Set.range (fieldBaseChangeMap C.boundaryOverHom kbar) from rfl, h2]
    show _ ⁻¹' Set.range C.j.base = (_ ⁻¹' Set.range C.boundaryι.base)ᶜ
    rw [C.range_j_eq_compl, Set.preimage_compl]
  exact perfectDerivedTrace_twistedFrobenius_extensionByZeroConstant_eq_zero Λ C.toOver
    (C.extendOver hjU a ha) kbar p q hcard C.j C.boundaryι C.range_j_eq_compl a.hom
    (C.isPullback_extend pU hjU a ha) (fieldBaseChangeMap C.openOverHom kbar)
    (fieldBaseChangeMap C.boundaryOverHom kbar) hij' (fieldBaseChangeProj C.boundaryOver kbar)
    (fieldBaseChangeMap_comp_fst C.boundaryOverHom kbar) (fieldBaseChangeProj C.openOver kbar)
    (fieldBaseChangeMap_comp_fst C.openOverHom kbar) N
    (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
    (fieldBaseChangeMap_comp_snd C.boundaryOverHom kbar).symm
    (twistedGeometricFrobenius C.boundaryOver (C.boundaryOverAut hjU a ha) kbar p q hcard)
    (twistedGeometricFrobenius_comp_toBase C.boundaryOver (C.boundaryOverAut hjU a ha) kbar p q
      hcard)
    (twistedGeometricFrobenius_comp_fieldBaseChangeMap_of_comm C.boundaryOverHom kbar p q hcard _ _
      (C.boundaryOverAut_comp_boundaryOverHom hjU a ha))
    (twistedGeometricFrobenius C.openOver (C.openOverAut hjU a ha) kbar p q hcard)
    (twistedGeometricFrobenius_comp_fieldBaseChangeMap_of_comm C.openOverHom kbar p q hcard _ _
      (C.openOverAut_comp_openOverHom hjU a ha))
    (fun y hy => not_comp_twistedGeometricFrobenius_eq kbar p q hcard (C.openOverToBase hjU)
      (C.openOverAut hjU a ha) (C.openOverAut_comp_openOverToBase hjU a ha) y
      (by rw [← fieldBaseChangeMap_comp_snd C.openOverHom kbar]; simpa using hy))
    hZ hp₂ hp₃ hΓ hweil

end Cover

end Stacks.EtaleCohomology

end
