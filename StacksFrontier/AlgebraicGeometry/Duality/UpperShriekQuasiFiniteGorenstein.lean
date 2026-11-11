module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseAssociatedSheaf
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.GorensteinInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulayTwistIso
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTraceSection
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# Dualizing modules along a quasi-finite Gorenstein morphism

Let `f : X ⟶ Y` be a quasi-finite Gorenstein morphism of schemes separated and of finite type
over a Noetherian base, with `X` Cohen–Macaulay and `f` étale at the generic points of `X`, and let
`R ⊆ X` be the closed subscheme cut out by the different. The relative dualizing module is
`ω_{X/Y} = 𝒪_X(R)` (Tag 0C17), it is `H⁰(f^!𝒪_Y)` (Tag 0BUL), and when `f` is finite the
isomorphism `𝒪_X(R) = ω_{X/Y}` sends the canonical section to the section dual to `Trace_f`
(Tag 0BVI).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A Cohen–Macaulay locally Noetherian scheme has no embedded points. -/
theorem hasNoEmbeddedPoints_of_isCohenMacaulay (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : IsCohenMacaulay X) : HasNoEmbeddedPoints X := by
  have h1 : HasPropertySk X 1 := (isCohenMacaulay_iff_forall_hasPropertySk X).1 hX 1
  let F := SheafOfModules.unit X.ringCatSheaf
  have : F.IsCoherent := by
    dsimp [F]
    infer_instance
  rw [← AlgebraicGeometry.structureSheaf_sheafHasPropertySk_one_iff X] at h1
  simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint] using
    (hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one X F).2 h1

end AlgebraicGeometry

namespace Stacks.Duality

open DerivedPushforward Stacks.Discriminant

/-- The trace element of a relative dualizing module, as a `RelativeTraceSection`. -/
def relativeTraceSectionData {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [Flat f] (D : RelativeDualizingModuleData f) :
    RelativeTraceSection D where
  sect := relativeTraceSection D
  isTraceElement_localEquiv U V hVU := by
    let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    exact fun F => (isTraceElement_iff_eq_traceCandidate F _).2
      (localEquiv_relativeTraceSection D U V hVU F)

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)

/-- Étale at the generic points of a Cohen–Macaulay source is étale at its associated points. -/
theorem etaleAt_of_mem_schemeAssociatedPoints (hX : IsCohenMacaulay X.left)
    (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x) :
    ∀ x ∈ Stacks.Divisors.schemeAssociatedPoints X.left, EtaleAt f.left x := by
  rw [schemeAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X.left
    (hasNoEmbeddedPoints_of_isCohenMacaulay X.left hX)]
  exact hét

/-- **Stacks Project, Tag 0C18, the finite case.** Let `f : X ⟶ Y` be a finite Gorenstein
morphism of schemes separated and of finite type over a Noetherian base, with `X` Cohen–Macaulay
and `f` étale at the generic points of `X`, and let `R ⊆ X` be cut out by the different of the
relative dualizing module `ω_{X/Y} = H⁰(f^!𝒪_Y)` of Tag 0BUL. Then the isomorphism
`𝒪_X(R) ≅ ω_{X/Y}` of Tag 0C17 is the unique one sending the canonical section `1_R` to the
section `τ_{X/Y}` of `H⁰(f^!𝒪_Y)` corresponding under duality to `Trace_f : f_*𝒪_X ⟶ 𝒪_Y`
(Tag 0BVI). -/
@[stacks 0C18 "if f is finite: O_X(R) = omega_{X/Y} comes from tau_{X/Y}, dual to Trace_f"]
theorem existsUnique_invertibleSheafIso_upperShriekDualSection [IsFinite f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    (j : CompactificationOf (Over.mk f.left)) :
    letI : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
      (isLocallyNoetherian_fiber_left f)).mp hGor).1
    ∃! e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf
        (upperShriekRelativeDualizingModuleData f j)
        (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j))) ≅
        (upperShriekRelativeDualizingModuleData f j).sheaf,
      Scheme.Modules.Hom.app e.hom ⊤
          ((Stacks.Divisors.canonicalSection' (differentIdealSheaf
            (upperShriekRelativeDualizingModuleData f j)
            (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j)))).eval
              (op ⊤)) =
        upperShriekDualSection f (pushforwardTrace f.left) j := by
  let : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
    (isLocallyNoetherian_fiber_left f)).mp hGor).1
  rw [upperShriekDualSection_pushforwardTrace f j]
  exact (isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein f.left hGor
    (upperShriekRelativeDualizingModuleData f j) (etaleAt_of_mem_schemeAssociatedPoints f hX hét)
    (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j))).2

section Comparison

variable [LocallyQuasiFinite f.left] (j : CompactificationOf (Over.mk f.left))
  (ω : RelativeDualizingModuleData f.left)

/-- Transport an isomorphism `A ≅ F ω_{X/Y}` to one with `F 𝒪_X(R)`, for `R` cut out by the
different. -/
private theorem nonempty_iso_and_iso_invertibleSheaf_of_isGorenstein {C : Type*} [Category C]
    [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω)
    (F : X.left.Modules ⥤ C) {A : C} (e : A ≅ F.obj ω.sheaf) :
    Nonempty (A ≅ F.obj ω.sheaf) ∧
      Nonempty (A ≅ F.obj (Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ))) := by
  exact ⟨⟨e⟩, ⟨e ≪≫ F.mapIso
    ((isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein f.left hGor ω
      (etaleAt_of_mem_schemeAssociatedPoints f hX hét) τ).2.exists.choose).symm⟩⟩

/-- The canonical isomorphism `H⁰(f^!𝒪_Y) ≅ ω_{X/Y}` of Tag 0BUL with a relative dualizing module,
as an isomorphism of sheaves of modules. -/
def upperShriekStructureSheafZerothIsoOfData : upperShriekStructureSheafZeroth f j ≅ ω.sheaf :=
  let E := (existsUnique_upperShriekRelativeDualizingComparison f j ω).exists.choose
  have hE := (existsUnique_upperShriekRelativeDualizingComparison f j ω).exists.choose_spec.1
  (Stacks.Veronese.exists_moduleSheafIso_of_sectionIso_onBasis.{u, u}
    (upperShriekStructureSheafZeroth f j) ω.sheaf (fun W : X.left.Opens => W)
    (by
      rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
      exact fun {W} {x} hx => ⟨W, Set.mem_range_self W, hx, le_rfl⟩)
    (fun W => (E W).toModuleIso) (fun W W' h s => hE W W' h s)).choose

/-- `ω_{X/Y}` of Tag 0C10 in relative dimension `0` is `H⁰(f^!𝒪_Y)`. -/
def relativeDualizingSheafZeroIso :
    relativeDualizingSheaf f j 0 ≅ upperShriekStructureSheafZeroth f j :=
  eqToIso (congrArg (fun n : ℤ => (DerivedCategory.homologyFunctor X.left.Modules n).obj
    (relativeDualizingComplexObj f j)) (by simp))

/-- **Stacks Project, Tag 0C18, granted `μ_{f,K}` and that `ω_Y^•` is dualizing.** Let
`f : X ⟶ Y` be a quasi-finite Gorenstein morphism of `FTS S`, with `X` and `Y` Cohen–Macaulay,
`Y` connected and `f` étale at the generic points of `X`; let `ω_Y^• = π_Y^!ω_T` and
`ω_X^• = π_X^!ω_T`. Then both are concentrated in one degree `m`, and for every relative
dualizing module `ω_{X/Y}` with trace element `τ` and different `R`,
`ω_X ≅ f^*ω_Y ⊗ ω_{X/Y} ≅ f^*ω_Y ⊗ 𝒪_X(R)`. -/
theorem exists_dualizingModule_iso_of_quasiFinite_of_isGorenstein_of_iso
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    [ConnectedSpace Y.left] (hY : IsCohenMacaulay Y.left)
    (hωY : IsDualizingComplex ((upperShriek πY jY).obj ωT).obj)
    (μ : ((quasiCoherentDerivedTensor X.left).obj
        ((quasiCoherentDerivedPullback' f.left).obj ((upperShriek πY jY).obj ωT))).obj
          ((upperShriek f j).obj (derivedStructureSheaf Y.left)) ≅
        (upperShriek f j).obj ((upperShriek πY jY).obj ωT)) :
    letI : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
      (isLocallyNoetherian_fiber_left f)).mp hGor).1
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((upperShriek πY jY).obj ωT).obj)) ∧
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        ((upperShriek πX jX).obj ωT).obj)) ∧
      ∀ (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω),
        Nonempty ((DerivedCategory.homologyFunctor X.left.Modules m).obj
            ((upperShriek πX jX).obj ωT).obj ≅
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
            ((Scheme.Modules.pullback f.left).obj
              ((DerivedCategory.homologyFunctor Y.left.Modules m).obj
                ((upperShriek πY jY).obj ωT).obj))).obj ω.sheaf) ∧
        Nonempty ((DerivedCategory.homologyFunctor X.left.Modules m).obj
            ((upperShriek πX jX).obj ωT).obj ≅
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
            ((Scheme.Modules.pullback f.left).obj
              ((DerivedCategory.homologyFunctor Y.left.Modules m).obj
                ((upperShriek πY jY).obj ωT).obj))).obj
            (Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ))) := by
  let : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
    (isLocallyNoetherian_fiber_left f)).mp hGor).1
  obtain ⟨m, h1, h2, ⟨e⟩⟩ := exists_homology_upperShriek_comp_iso_pullback_tensor_of_iso f j
    (Scheme.Hom.isCohenMacaulay_of_isGorenstein f.left _ hGor) 0
    (fun x => topologicalKrullDimAt_fiber_eq_zero f.left x) πY πX hπ jY jX ωT hωT hY hωY μ
  rw [show m - ((0 : ℕ) : ℤ) = m by simp] at h2 e
  refine ⟨m, h1, h2, fun ω τ => ?_⟩
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
    ((Scheme.Modules.pullback f.left).obj
      ((DerivedCategory.homologyFunctor Y.left.Modules m).obj ((upperShriek πY jY).obj ωT).obj))
  have e₁ := e ≪≫ F.mapIso ((relativeDualizingSheafZeroIso f j) ≪≫
    upperShriekStructureSheafZerothIsoOfData f j ω)
  exact nonempty_iso_and_iso_invertibleSheaf_of_isGorenstein f hGor hX hét ω τ F e₁

/-- **The isomorphism `𝒪_X(R) ≅ ω_{X/Y}` of Tag 0C17 (6).** For a quasi-finite Gorenstein
morphism `f` étale at the generic points of a Cohen–Macaulay `X`, a relative dualizing module
`ω_{X/Y}` with trace element `τ` and `R` cut out by the different, this is the unique isomorphism
`𝒪_X(R) ≅ ω_{X/Y}` sending the canonical section `1_R` to `τ`
(`invertibleSheafIsoOfIsGorenstein_hom_app_canonicalSection`,
`eq_invertibleSheafIsoOfIsGorenstein`). -/
def invertibleSheafIsoOfIsGorenstein [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω) :
    Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ) ≅ ω.sheaf :=
  ((isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein f.left hGor ω
    (etaleAt_of_mem_schemeAssociatedPoints f hX hét) τ).2.exists.choose)

/-- `invertibleSheafIsoOfIsGorenstein` sends the canonical section `1_R` to the trace
element `τ`. -/
theorem invertibleSheafIsoOfIsGorenstein_hom_app_canonicalSection [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω) :
    Scheme.Modules.Hom.app (invertibleSheafIsoOfIsGorenstein f hGor hX hét ω τ).hom ⊤
        ((Stacks.Divisors.canonicalSection' (differentIdealSheaf ω τ)).eval (op ⊤)) = τ.sect :=
  ((isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein f.left hGor ω
    (etaleAt_of_mem_schemeAssociatedPoints f hX hét) τ).2.exists.choose_spec)

/-- An isomorphism `𝒪_X(R) ≅ ω_{X/Y}` sending `1_R` to `τ` is
`invertibleSheafIsoOfIsGorenstein`. -/
theorem eq_invertibleSheafIsoOfIsGorenstein [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω)
    (e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ) ≅ ω.sheaf)
    (he : Scheme.Modules.Hom.app e.hom ⊤
        ((Stacks.Divisors.canonicalSection' (differentIdealSheaf ω τ)).eval (op ⊤)) = τ.sect) :
    e = invertibleSheafIsoOfIsGorenstein f hGor hX hét ω τ :=
  (isEffectiveCartierDivisor_and_invertibleSheafIso_of_isGorenstein f.left hGor ω
    (etaleAt_of_mem_schemeAssociatedPoints f hX hét) τ).2.unique he
    (invertibleSheafIsoOfIsGorenstein_hom_app_canonicalSection f hGor hX hét ω τ)

/-- **Stacks Project, Tag 0C18, the finite case, for the named isomorphism.** If `f` is
moreover finite and `ω_{X/Y} = H⁰(f^!𝒪_Y)` (Tag 0BUL) with its trace element, the isomorphism
`invertibleSheafIsoOfIsGorenstein : 𝒪_X(R) ≅ ω_{X/Y}` sends `1_R` to the section `τ_{X/Y}` of
`H⁰(f^!𝒪_Y)` corresponding under duality to `Trace_f : f_*𝒪_X ⟶ 𝒪_Y` (Tag 0BVI). -/
@[stacks 0C18 "if f is finite: the named iso O_X(R) = omega_{X/Y} sends 1_R to tau_{X/Y}, dual \
  to Trace_f"]
theorem invertibleSheafIsoOfIsGorenstein_hom_app_eq_upperShriekDualSection [IsFinite f.left]
    [Flat f.left] (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x) :
    Scheme.Modules.Hom.app (invertibleSheafIsoOfIsGorenstein f hGor hX hét
        (upperShriekRelativeDualizingModuleData f j)
        (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j))).hom ⊤
        ((Stacks.Divisors.canonicalSection' (differentIdealSheaf
          (upperShriekRelativeDualizingModuleData f j)
          (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j)))).eval
            (op ⊤)) =
      upperShriekDualSection f (pushforwardTrace f.left) j := by
  rw [upperShriekDualSection_pushforwardTrace f j]
  exact invertibleSheafIsoOfIsGorenstein_hom_app_canonicalSection f hGor hX hét _ _

/-- **Stacks Project, Tag 0C18, the isomorphism `ω_X ≅ f^*ω_Y ⊗ ω_{X/Y}`.** Let `f : X ⟶ Y`
be a quasi-finite Gorenstein morphism of `FTS S`, `πX = f ≫ πY` and `ω_T` bounded below, with
`ω_Y^• = π_Y^!ω_T` and `ω_X^• = π_X^!ω_T`, and let `ω_{X/Y}` be a relative dualizing module.
In every degree `i` this is the composite
`Hⁱ(ω_X^•) ≅ Hⁱ(Lf^*ω_Y^• ⊗ᴸ H⁰(f^!𝒪_Y)[0]) ≅ f^*Hⁱ(ω_Y^•) ⊗ H⁰(f^!𝒪_Y) ≅ f^*Hⁱ(ω_Y^•) ⊗ ω_{X/Y}`
of
* `Hⁱ` of the isomorphism `ω_X^• ≅ Lf^*ω_Y^• ⊗ᴸ ω_{X/Y}[0]` of Tag 0C10
  (`upperShriekCompIsoPullbackTensorShiftOfIso`: the composition isomorphism
  `(f ≫ πY)^! ≅ f^!πY^!`, the inverse of the canonical comparison `μ_{f,ω_Y^•}` of Tag 0B6U,
  which is an isomorphism since `f` is perfect, and the concentration `f^!𝒪_Y ≅ H⁰(f^!𝒪_Y)[0]`);
* the flat cohomology isomorphism `Hⁱ(Lf^*K ⊗ᴸ G[0]) ≅ f^*Hⁱ(K) ⊗ G`
  (`homologyDerivedTensorDerivedPullbackIso`, `H⁰(f^!𝒪_Y)` being flat over `Y`);
* the isomorphism `H⁰(f^!𝒪_Y) ≅ ω_{X/Y}` of Tag 0BUL (`upperShriekStructureSheafZerothIsoOfData`).

The auxiliary choices (a K-flat resolution, a representative complex, a complex in degree `0`)
are made inside these constructions. -/
@[stacks 0C18 "the composite isomorphism omega_X = f^* omega_Y (x) omega_{X/Y}, combining 0C10, \
  the flat cohomology iso and 0BUL"]
def homologyUpperShriekCompIsoPullbackTensor [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    (i : ℤ) (ω : RelativeDualizingModuleData f.left) :
    (DerivedCategory.homologyFunctor X.left.Modules i).obj ((upperShriek πX jX).obj ωT).obj ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
        ((Scheme.Modules.pullback f.left).obj
          ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
            ((upperShriek πY jY).obj ωT).obj))).obj ω.sheaf := by
  have hCM := Scheme.Hom.isCohenMacaulay_of_isGorenstein f.left _ hGor
  have := perfect_of_isCohenMacaulay f hCM
  have := isIso_upperShriekCompareWithPullback f j ((upperShriek πY jY).obj ωT)
    (isBoundedBelow_upperShriek_obj πY jY ωT hωT)
  let eX := upperShriekCompIsoPullbackTensorShiftOfIso f j hCM 0
    (fun x => topologicalKrullDimAt_fiber_eq_zero f.left x) πY πX hπ jY jX ωT hωT
    (asIso (upperShriekCompareWithPullbackCanonical f j ((upperShriek πY jY).obj ωT)))
  let W := relativeDualizingSheaf f j 0
  have hW : IsFlatOver f.left.toLRSHom.toShHom W :=
    isFlatOver_homology_of_isCohenMacaulay (upperShriekStructureSheafCharts f j) hCM _
  let e0 : (((DerivedCategory.singleFunctor X.left.Modules 0).obj W)⟦((0 : ℕ) : ℤ)⟧) ≅
      (DerivedCategory.singleFunctor X.left.Modules 0).obj W :=
    (shiftFunctorZero' (DerivedCategory X.left.Modules) ((0 : ℕ) : ℤ) (by simp)).app _
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
    ((Scheme.Modules.pullback f.left).obj
      ((DerivedCategory.homologyFunctor Y.left.Modules i).obj ((upperShriek πY jY).obj ωT).obj))
  exact (DerivedCategory.homologyFunctor X.left.Modules i).mapIso ((ObjectProperty.ι _).mapIso eX ≪≫
      ((derivedTensor X.left).obj
        ((derivedPullback f.left).obj ((upperShriek πY jY).obj ωT).obj)).mapIso e0) ≪≫
    homologyDerivedTensorDerivedPullbackIso f.left ((upperShriek πY jY).obj ωT).obj W hW i ≪≫
    F.mapIso (relativeDualizingSheafZeroIso f j ≪≫ upperShriekStructureSheafZerothIsoOfData f j ω)

/-- **Stacks Project, Tag 0C18, the isomorphism `ω_X ≅ f^*ω_Y ⊗ 𝒪_X(R)`.** In the situation of
`homologyUpperShriekCompIsoPullbackTensor`, with `X` Cohen–Macaulay, `f` étale at the generic
points of `X`, `τ` the trace element of `ω_{X/Y}` and `R` cut out by the different: in every
degree `i`, the isomorphism `Hⁱ(ω_X^•) ≅ f^*Hⁱ(ω_Y^•) ⊗ ω_{X/Y}` followed by `f^*Hⁱ(ω_Y^•) ⊗ -`
of the inverse of the isomorphism `𝒪_X(R) ≅ ω_{X/Y}` of Tag 0C17
(`invertibleSheafIsoOfIsGorenstein`, the unique one sending `1_R` to `τ`). -/
@[stacks 0C18 "the composite isomorphism omega_X = f^* omega_Y (x) O_X(R), through 0C17"]
def homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf [Flat f.left]
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    (i : ℤ) (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω) :
    (DerivedCategory.homologyFunctor X.left.Modules i).obj ((upperShriek πX jX).obj ωT).obj ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
        ((Scheme.Modules.pullback f.left).obj
          ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
            ((upperShriek πY jY).obj ωT).obj))).obj
        (Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ)) :=
  homologyUpperShriekCompIsoPullbackTensor f j hGor πY πX hπ jY jX ωT hωT i ω ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
      ((Scheme.Modules.pullback f.left).obj
        ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
          ((upperShriek πY jY).obj ωT).obj))).mapIso
      (invertibleSheafIsoOfIsGorenstein f hGor hX hét ω τ).symm

/-- **Stacks Project, Tag 0C18.** Let `S` be Noetherian, `f : X ⟶ Y` a quasi-finite Gorenstein
morphism of `FTS S`, with `X` and `Y` Cohen–Macaulay, `Y` connected and `f` étale at the generic
points of `X`; let `ω_T` be a dualizing complex, `πX = f ≫ πY`, `ω_Y^• = π_Y^!ω_T` and
`ω_X^• = π_X^!ω_T`. Then both are concentrated in one degree `m`, so their cohomology sheaves
`ω_Y`, `ω_X` there are the dualizing modules, and for every relative dualizing module `ω_{X/Y}`
with trace element `τ` and different `R`, the canonical isomorphism
`homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf : ω_X ≅ f^*ω_Y ⊗ 𝒪_X(R)` is
`homologyUpperShriekCompIsoPullbackTensor : ω_X ≅ f^*ω_Y ⊗ ω_{X/Y}` (from Tag 0C10) followed by
`f^*ω_Y ⊗ -` of the inverse of any isomorphism `𝒪_X(R) ≅ ω_{X/Y}` sending `1_R` to `τ`
(Tag 0C17). -/
@[stacks 0C18 "the canonical iso omega_X = f^* omega_Y (x) omega_{X/Y} = f^* omega_Y (x) O_X(R) \
  in the degree of the dualizing modules"]
theorem exists_isZero_homology_and_homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf_eq
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : IsDualizingComplex ωT.obj)
    [ConnectedSpace Y.left] (hY : IsCohenMacaulay Y.left) :
    letI : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
      (isLocallyNoetherian_fiber_left f)).mp hGor).1
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
        ((upperShriek πY jY).obj ωT).obj)) ∧
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        ((upperShriek πX jX).obj ωT).obj)) ∧
      ∀ (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω)
        (e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ) ≅ ω.sheaf),
        Scheme.Modules.Hom.app e.hom ⊤
            ((Stacks.Divisors.canonicalSection' (differentIdealSheaf ω τ)).eval (op ⊤)) =
          τ.sect →
        homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf f j hGor hX hét πY πX hπ jY jX ωT
            (isBoundedBelow_of_isDualizingComplex _ hωT) m ω τ =
          homologyUpperShriekCompIsoPullbackTensor f j hGor πY πX hπ jY jX ωT
              (isBoundedBelow_of_isDualizingComplex _ hωT) m ω ≪≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
              ((Scheme.Modules.pullback f.left).obj
                ((DerivedCategory.homologyFunctor Y.left.Modules m).obj
                  ((upperShriek πY jY).obj ωT).obj))).mapIso e.symm := by
  let : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
    (isLocallyNoetherian_fiber_left f)).mp hGor).1
  obtain ⟨m, h1, h2, -⟩ := exists_homology_upperShriek_comp_iso_pullback_tensor f j
    (Scheme.Hom.isCohenMacaulay_of_isGorenstein f.left _ hGor) 0
    (fun x => topologicalKrullDimAt_fiber_eq_zero f.left x) πY πX hπ jY jX ωT hωT hY
  refine ⟨m, h1, fun i hi => h2 i (by simpa using hi), fun ω τ e he => ?_⟩
  obtain rfl := eq_invertibleSheafIsoOfIsGorenstein f hGor hX hét ω τ e he
  rfl

/-- **Stacks Project, Tag 0C18, existence form.** Let `S` be Noetherian, `f : X ⟶ Y` a
quasi-finite Gorenstein morphism of `FTS S` étale at the generic points of `X`, with `X`
Cohen–Macaulay, and let
`ω_Y^• = π_Y^!ω_T`, `ω_X^• = π_X^!ω_T` for `π_X = f ≫ π_Y` and `ω_T` bounded below (for instance
a dualizing complex on the base). Let `ω_{X/Y}` be any relative dualizing module (Tag 0BVG; by
Tag 0BUL it is `H⁰(f^!𝒪_Y)`), `τ` its trace element and `R` the closed subscheme cut out by the
different. Then in every degree `i`
`Hⁱ(ω_X^•) ≅ f^*Hⁱ(ω_Y^•) ⊗ ω_{X/Y} ≅ f^*Hⁱ(ω_Y^•) ⊗ 𝒪_X(R)`.
When `X` and `Y` are Cohen–Macaulay and `ω_T` is dualizing, `ω_X^•` and `ω_Y^•` have a single
nonzero cohomology sheaf on each connected component, in the same degree; `ω_X` and `ω_Y` are
these sheaves, and the displayed isomorphisms are `ω_X = f^*ω_Y ⊗ ω_{X/Y} = f^*ω_Y ⊗ 𝒪_X(R)`.

This only asserts that the isomorphisms exist; the canonical isomorphisms of the remark are the
named maps `homologyUpperShriekCompIsoPullbackTensor` and
`homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf` (computed here at the chosen
compactification of `f`), described in
`exists_isZero_homology_and_homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf_eq`. -/
@[stacks 0C18 "existence form: omega_X = f^* omega_Y (x) omega_{X/Y} = f^* omega_Y (x) O_X(R) \
  hold in every degree; the canonical maps are homologyUpperShriekCompIsoPullbackTensor and \
  homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf"]
theorem nonempty_homology_upperShriek_iso_pullback_tensor_of_isGorenstein
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj)
    (i : ℤ) :
    letI : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
      (isLocallyNoetherian_fiber_left f)).mp hGor).1
    ∀ (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω),
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
              ((upperShriek πY jY).obj ωT).obj))).obj ω.sheaf) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
              ((upperShriek πY jY).obj ωT).obj))).obj
          (Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ))) := by
  let : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
    (isLocallyNoetherian_fiber_left f)).mp hGor).1
  intro ω τ
  let j := (chosenOpenFiniteFactorization f).compactification
  exact ⟨⟨homologyUpperShriekCompIsoPullbackTensor f j hGor πY πX hπ jY jX ωT hωT i ω⟩,
    ⟨homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf f j hGor hX hét πY πX hπ jY jX ωT hωT
      i ω τ⟩⟩

/-- **Stacks Project, Tag 0C18**, the whole remark. Let `S` be Noetherian and `f : X ⟶ Y` a
quasi-finite Gorenstein morphism of schemes separated and of finite type over `S`, with `X`
Cohen–Macaulay and `f` étale at the generic points of `X`. Let `ω_Y^• = π_Y^!ω_T` and
`ω_X^• = π_X^!ω_T` for `π_X = f ≫ π_Y` and a bounded below `ω_T` (for instance `T = S` with its
dualizing complex `ω_S^•`, which gives the normalized dualizing complexes). Then:

1. for every relative dualizing module `ω_{X/Y}` (Tag 0BVG; by Tag 0BUL it is `H⁰(f^!𝒪_Y)`),
   with trace element `τ` and `R` the closed subscheme cut out by the different, in every degree
   `i` one has `Hⁱ(ω_X^•) ≅ f^*Hⁱ(ω_Y^•) ⊗ ω_{X/Y} ≅ f^*Hⁱ(ω_Y^•) ⊗ 𝒪_X(R)`; in the degree of the
   dualizing modules this is `ω_X = f^*ω_Y ⊗ ω_{X/Y} = f^*ω_Y ⊗ 𝒪_X(R)`;
2. if moreover `f` is finite, the isomorphism `𝒪_X(R) ≅ ω_{X/Y} = H⁰(f^!𝒪_Y)` is the unique one
   sending the canonical section `1_R` to the section `τ_{X/Y}` which corresponds under duality to
   `Trace_f : f_*𝒪_X ⟶ 𝒪_Y` (Tag 0BVI).

Part 1 is stated in existence form; the canonical isomorphisms are
`homologyUpperShriekCompIsoPullbackTensor` and
`homologyUpperShriekCompIsoPullbackTensorInvertibleSheaf`. -/
@[stacks 0C18 "the whole remark, part 1 in existence form: omega_X = f^* omega_Y (x) \
  omega_{X/Y} = f^* omega_Y (x) O_X(R), and for f finite O_X(R) = omega_{X/Y} comes from \
  tau_{X/Y}, dual to Trace_f"]
theorem upperShriek_quasiFinite_isGorenstein_dualizing_iso
    (hGor : f.left.IsGorenstein (isLocallyNoetherian_fiber_left f))
    (hX : IsCohenMacaulay X.left) (hét : ∀ x ∈ genericPoints X.left, EtaleAt f.left x)
    {T : FTS S} (πY : Y ⟶ T) (πX : X ⟶ T) (hπ : f ≫ πY = πX)
    (jY : CompactificationOf (Over.mk πY.left)) (jX : CompactificationOf (Over.mk πX.left))
    (ωT : quasiCoherentDerivedCategory T.left) (hωT : DerivedCategoryB.IsBoundedBelow ωT.obj) :
    letI : Flat f.left := ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber f.left
      (isLocallyNoetherian_fiber_left f)).mp hGor).1
    (∀ (i : ℤ) (ω : RelativeDualizingModuleData f.left) (τ : RelativeTraceSection ω),
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
              ((upperShriek πY jY).obj ωT).obj))).obj ω.sheaf) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          ((upperShriek πX jX).obj ωT).obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.left.sheaf).obj
          ((Scheme.Modules.pullback f.left).obj
            ((DerivedCategory.homologyFunctor Y.left.Modules i).obj
              ((upperShriek πY jY).obj ωT).obj))).obj
          (Stacks.Divisors.invertibleSheaf' (differentIdealSheaf ω τ)))) ∧
    ∀ [IsFinite f.left] (j : CompactificationOf (Over.mk f.left)),
      ∃! e : Stacks.Divisors.invertibleSheaf' (differentIdealSheaf
          (upperShriekRelativeDualizingModuleData f j)
          (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j))) ≅
          (upperShriekRelativeDualizingModuleData f j).sheaf,
        Scheme.Modules.Hom.app e.hom ⊤
            ((Stacks.Divisors.canonicalSection' (differentIdealSheaf
              (upperShriekRelativeDualizingModuleData f j)
              (relativeTraceSectionData (upperShriekRelativeDualizingModuleData f j)))).eval
                (op ⊤)) =
          upperShriekDualSection f (pushforwardTrace f.left) j := by
  refine ⟨fun i => nonempty_homology_upperShriek_iso_pullback_tensor_of_isGorenstein f hGor hX hét
    πY πX hπ jY jX ωT hωT i, ?_⟩
  intro _ j
  exact existsUnique_invertibleSheafIso_upperShriekDualSection f hGor hX hét j

end Comparison

end Stacks.Duality
