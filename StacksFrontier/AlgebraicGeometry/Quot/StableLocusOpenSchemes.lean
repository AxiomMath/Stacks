module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingSheafCurveFibres
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenFibreAmple
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties

/-!
# Openness of the stable locus of a family of nodal curves (schemes)

Let `f : X ⟶ S` be a proper flat morphism of finite presentation of schemes, `S` quasi-compact
and quasi-separated, whose fibres are Gorenstein and equidimensional of dimension one. The
relative dualizing sheaf `ω_{X/S}` is invertible and restricts on every fibre `X_s` to its
dualizing sheaf `ω_{X_s}` (Stacks 0E6P, 0E6R). If `ω_{X_s}` is ample, then by Stacks 0D2S
`ω_{X/S}` is relatively ample over a neighbourhood `V` of `s`, hence `ω_{X_t}` is ample for every
`t ∈ V`: the locus of points whose fibre has an ample dualizing sheaf is open.

For a family of nodal curves with `H⁰(X_s, 𝒪) = κ(s)`, an ample dualizing sheaf is the same as
being stable (Stacks 0E76 (2)(b) ⟺ (c)), so the stable locus is open. This is the step
"(2) ⟹ ... after shrinking, `Y → U` is a stable family" of Stacks 0E74 and of the proof of
Stacks 0E8A, for families whose total space is a scheme.

Stacks 0E74 and 0E76 are stated for families of curves over algebraic spaces; that form of the
result is `AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback`.

## Main results

* `AlgebraicGeometry.CurveFibres.exists_isPullback_morphismRestrict_of_isPullback`: a base change
  landing in an open `V ⊆ S` is a base change of `f⁻¹(V) ⟶ V`.
* `AlgebraicGeometry.CurveFibres.exists_mem_forall_isAmple_dualizingSheafOverField`: ampleness of
  the dualizing sheaf spreads from a fibre to the fibres over a neighbourhood.
* `AlgebraicGeometry.CurveFibres.exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge`:
  stability spreads from a fibre to the fibres over a neighbourhood, for nodal families with
  `H⁰ = κ` on the fibres.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality Stacks.Duality.CurveFibres
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.CurveFibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **A base change landing in an open is a base change of the restriction.** For a cartesian
square presenting `C` as `X ×_S K` and an open `V ⊆ S` containing the image of `K ⟶ S`, the
square factors through `f⁻¹(V) ⟶ V` and the factored square is cartesian. -/
theorem exists_isPullback_morphismRestrict_of_isPullback {C K : Scheme.{u}} {h : C ⟶ X}
    {g : C ⟶ K} {c : K ⟶ S} (hpb : IsPullback h g f c) (V : S.Opens)
    (hcV : Set.range c ⊆ V) :
    ∃ (a : C ⟶ (f ⁻¹ᵁ V).toScheme) (c' : K ⟶ V.toScheme),
      a ≫ (f ⁻¹ᵁ V).ι = h ∧ IsPullback a g (f ∣_ V) c' := by
  have hc' : Set.range c ⊆ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  have ha' : Set.range h ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : f.base (h.base x) = c.base (g.base x) := by
      simp only [← Scheme.Hom.comp_apply, hpb.w]
    change f.base (h.base x) ∈ (V : Set S)
    exact hx ▸ hcV ⟨_, rfl⟩
  have hc := IsOpenImmersion.lift_fac V.ι c hc'
  have ha := IsOpenImmersion.lift_fac (f ⁻¹ᵁ V).ι h ha'
  have hsq : IsOpenImmersion.lift (f ⁻¹ᵁ V).ι h ha' ≫ (f ∣_ V) =
      g ≫ IsOpenImmersion.lift V.ι c hc' := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hc, morphismRestrict_ι,
      ← Category.assoc, ha, hpb.w]
  refine ⟨_, _, ha, IsPullback.of_right ?_ hsq (isPullback_morphismRestrict f V).flip⟩
  rwa [ha, hc]

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f]

/-- The relative dualizing sheaf of a family with Gorenstein fibres equidimensional of dimension
one is invertible (Stacks 0E6R), as a `Stacks.Ample.IsInvertibleModule`. -/
theorem isInvertibleModule_properFlatDualizingSheaf (hG : HasGorensteinCurveFibres f) :
    Stacks.Ample.IsInvertibleModule X (properFlatDualizingSheaf f) :=
  Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _
    (isFiniteLocallyFreeOfRank_properFlatDualizingSheaf f hG)

/-- **Ampleness of the dualizing sheaf spreads from a fibre to a neighbourhood** (Stacks 0D2S
applied to `ω_{X/S}`, Stacks 0E6R). Let `f` be proper, flat, of finite presentation, with
Gorenstein fibres equidimensional of dimension one, and let `s ∈ S` be a point whose fibre,
presented by a scheme `C₀` over `Spec κ(s)`, has an invertible and ample dualizing sheaf. Then
there is an open neighbourhood `V` of `s` such that for every field `k`, every `Spec k ⟶ S`
landing in `V` and every scheme `C` presenting `X ×_S Spec k` which is Gorenstein and
equidimensional of dimension one, the dualizing sheaf `ω_C` is invertible and ample. -/
theorem exists_mem_forall_isAmple_dualizingSheafOverField (hG : HasGorensteinCurveFibres f)
    (s : S)
    (hs : ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ X) (g₀ : C₀ ⟶ Spec (.of (S.residueField s)))
      (_ : IsPullback h₀ g₀ f (S.fromSpecResidueField s)) (_ : IsProper g₀),
      (AlgebraicGeometry.IsGorenstein C₀ ∧ TopologicalSpace.Equidimensional C₀ ∧
        topologicalKrullDim C₀ = 1) ∧
      ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible C₀.toRingedSpace.presheaf
          (structureSheafRing C₀.toRingedSpace).property (dualizingSheafOverField g₀),
        Scheme.Modules.IsAmple C₀ (dualizingSheafOverField g₀)) :
    ∃ V : S.Opens, s ∈ V ∧ ∀ (k : Type u) [Field k] (C : Scheme.{u}) (h : C ⟶ X)
      (g : C ⟶ Spec (.of k)) (c : Spec (.of k) ⟶ S) (_ : IsPullback h g f c) [IsProper g],
      Set.range c ⊆ V →
      (AlgebraicGeometry.IsGorenstein C ∧ TopologicalSpace.Equidimensional C ∧
        topologicalKrullDim C = 1) →
      ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property (dualizingSheafOverField g),
        Scheme.Modules.IsAmple C (dualizingSheafOverField g) := by
  have := isInvertibleModule_properFlatDualizingSheaf f hG
  obtain ⟨C₀, h₀, g₀, hpb₀, _, hC₀, hinv, hamp⟩ := hs
  let e₀ := (nonempty_pullback_properFlatDualizingSheaf_iso_of_isPullback f hG hpb₀ hC₀).some
  have : Stacks.Ample.IsInvertibleModule C₀ (dualizingSheafOverField g₀) := hinv
  have h₀' : Stacks.Ample.IsAmple C₀ (pullbackModule h₀ (properFlatDualizingSheaf f)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e₀).2
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).2 hamp)
  have hι : hpb₀.isoPullback.inv ≫ h₀ = f.fiberι s := IsPullback.isoPullback_inv_fst hpb₀
  have : Stacks.Ample.IsInvertibleModule (f.fiber s)
      (pullbackModule (f.fiberι s) (properFlatDualizingSheaf f)) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback _ _
  have hs' : Stacks.Ample.IsAmple (f.fiber s)
      (pullbackModule (f.fiberι s) (properFlatDualizingSheaf f)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr (X := f.fiber s)
      (pullbackModule (f.fiberι s) (properFlatDualizingSheaf f))
      (pullbackModule hpb₀.isoPullback.inv (pullbackModule h₀ (properFlatDualizingSheaf f)))
      ((Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hι _).symm ≪≫
        Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ _)).2
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom hpb₀.isoPullback.inv _ h₀')
  obtain ⟨V, hsV, hrel⟩ := Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre f
    (properFlatDualizingSheaf f) s hs'
  refine ⟨V, hsV, fun k _ C h g c hpb _ hcV hC => ?_⟩
  obtain ⟨a, c', ha, hpb'⟩ := exists_isPullback_morphismRestrict_of_isPullback f hpb V hcV
  have h1 := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hpb' _ hrel
  have h2 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).1 h1
  let e2 : pullbackModule a (pullbackModule (f ⁻¹ᵁ V).ι (properFlatDualizingSheaf f)) ≅
      dualizingSheafOverField g :=
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso a (f ⁻¹ᵁ V).ι _).symm ≪≫
      Stacks.RelativeAmpleBaseChange.pullbackModuleCongr ha _ ≪≫
        (nonempty_pullback_properFlatDualizingSheaf_iso_of_isPullback f hG hpb hC).some
  have : Stacks.Ample.IsInvertibleModule C (dualizingSheafOverField g) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e2
  exact ⟨inferInstance, (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).1
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ e2).1 h2)⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] [Flat f] [LocallyOfFinitePresentation f] in
/-- A nodal curve over a field with `H⁰ = k` is Gorenstein and equidimensional of dimension one. -/
theorem isGorenstein_and_equidimensional_of_hasAtWorstNodalSingularities {k : Type u} [Field k]
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim C = 1)
    (hglob : Function.Bijective g.appTop)
    (hnodal : @Stacks.Curves.HasAtWorstNodalSingularities k _ C ⟨g⟩) :
    AlgebraicGeometry.IsGorenstein C ∧ TopologicalSpace.Equidimensional C ∧
      topologicalKrullDim C = 1 := by
  let : C.Over (Spec (.of k)) := ⟨g⟩
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper g)
  have : IsIso g.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hglob
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop) := inferInstance
  have : ConnectedSpace C := connectedSpace_of_isIso_globalSections k g
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : IsNoetherian C := {}
  exact ⟨isGorenstein_of_connectedSpace_of_hasAtWorstNodalSingularities _ _ hdim hnodal,
    equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim, hdim⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f] in
/-- **A presentation of a fibre of a nodal family with `H⁰ = κ`.** If `f` is at-worst-nodal of
relative dimension one and `C` presents the fibre over `Spec κ(t)` with `H⁰(C, 𝒪) = κ(t)`, then
`C` is nonempty, of dimension one, with at-worst-nodal singularities (Stacks 0C4D on the fibres,
via 0C59). -/
theorem dim_and_hasAtWorstNodalSingularities_of_isPullback
    (hnod : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne f) (t : S) {C : Scheme.{u}}
    {h : C ⟶ X} {g : C ⟶ Spec (.of (S.residueField t))}
    (hpb : IsPullback h g f (S.fromSpecResidueField t)) (hglob : Function.Bijective g.appTop) :
    topologicalKrullDim C = 1 ∧
      @Stacks.Curves.HasAtWorstNodalSingularities (S.residueField t) _ C ⟨g⟩ := by
  have : IsIso g.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hglob
  have : IsIso ((Scheme.ΓSpecIso (.of (S.residueField t))).inv ≫ g.appTop) := inferInstance
  have : Nonempty C := Stacks.Models.nonempty_of_isIso_globalSections g
  exact Stacks.Models.hasAtWorstNodalSingularities_of_isPullback_fiber hnod t hpb

/-- **Stability spreads from a fibre to a neighbourhood** (Stacks 0E74 (1) ⟹ (2) and the
openness of Stacks 0E76, for a family whose total space is a scheme). Let `f` be proper, flat, of
finite presentation and at-worst-nodal of relative dimension one, every fibre of which is presented
over `Spec κ(t)` by a scheme with `H⁰ = κ(t)`, and let `s ∈ S` be a point whose fibre, presented
by `C₀` with `H⁰(C₀, 𝒪) = κ(s)`, has genus at least two and neither a rational tail nor a rational
bridge. Then there is an open neighbourhood `V` of `s` such that every scheme `C` presenting a
fibre `X ×_S Spec k` over a field-valued point landing in `V`, which is nodal of dimension one
with `H⁰ = k`, has genus at least two and neither a rational tail nor a rational bridge. On such
curves stability is ampleness of the dualizing sheaf (Stacks 0E76 (2)(b) ⟺ (c)), which spreads
by Stacks 0D2S. -/
theorem exists_mem_forall_hasGenusTwoNoRationalTailNoRationalBridge
    (hnod : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne f)
    (hfib : ∀ t : S, ∃ (C : Scheme.{u}) (h : C ⟶ X) (g : C ⟶ Spec (.of (S.residueField t))),
      IsPullback h g f (S.fromSpecResidueField t) ∧ Function.Bijective g.appTop) (s : S)
    (hs : ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ X) (g₀ : C₀ ⟶ Spec (.of (S.residueField s))),
      IsPullback h₀ g₀ f (S.fromSpecResidueField s) ∧ Function.Bijective g₀.appTop ∧
        HasGenusTwoNoRationalTailNoRationalBridge (S.residueField s) g₀) :
    ∃ V : S.Opens, s ∈ V ∧ ∀ (k : Type u) [Field k] (C : Scheme.{u}) (h : C ⟶ X)
      (g : C ⟶ Spec (.of k)) (c : Spec (.of k) ⟶ S) (_ : IsPullback h g f c) [IsProper g],
      Set.range c ⊆ V → topologicalKrullDim C = 1 → Function.Bijective g.appTop →
      @Stacks.Curves.HasAtWorstNodalSingularities k _ C ⟨g⟩ →
      HasGenusTwoNoRationalTailNoRationalBridge k g := by
  have hG : HasGorensteinCurveFibres f := fun t => by
    obtain ⟨C, h, g, hpb, hglob⟩ := hfib t
    have : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) hpb inferInstance
    obtain ⟨hdim, hnodal⟩ := dim_and_hasAtWorstNodalSingularities_of_isPullback f hnod t hpb hglob
    exact ⟨C, h, g, hpb, isGorenstein_and_equidimensional_of_hasAtWorstNodalSingularities g hdim
      hglob hnodal⟩
  obtain ⟨C₀, h₀, g₀, hpb₀, hglob₀, hst₀⟩ := hs
  have : IsProper g₀ := MorphismProperty.of_isPullback (P := @IsProper) hpb₀ inferInstance
  obtain ⟨hdim₀, hnodal₀⟩ := dim_and_hasAtWorstNodalSingularities_of_isPullback f hnod s hpb₀ hglob₀
  obtain ⟨V, hsV, hV⟩ := exists_mem_forall_isAmple_dualizingSheafOverField f hG s
    ⟨C₀, h₀, g₀, hpb₀, inferInstance,
      isGorenstein_and_equidimensional_of_hasAtWorstNodalSingularities g₀ hdim₀ hglob₀ hnodal₀,
      (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField _ g₀ hdim₀
        hglob₀ hnodal₀).1 hst₀⟩
  refine ⟨V, hsV, fun k _ C h g c hpb _ hcV hdimC hglobC hnodC => ?_⟩
  exact (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField k g hdimC
    hglobC hnodC).2 (hV k C h g c hpb hcV
      (isGorenstein_and_equidimensional_of_hasAtWorstNodalSingularities g hdimC hglobC hnodC))

end AlgebraicGeometry.CurveFibres
