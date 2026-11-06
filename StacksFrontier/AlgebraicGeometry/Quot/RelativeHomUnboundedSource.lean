module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSpanIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# The relative Hom functor out of a free module of rank the cutoff is not an algebraic space

The first assertion of Stacks 08K6 reads: in Situation 08JT, if `f` is of finite presentation
and `G` is a finitely presented `𝒪_X`-module, flat over `B`, with support proper over `B`, then
`Hom(F, G)` is an algebraic space affine over `B`, for every quasi-coherent `F`. On a big fppf
site, whose schemes are bounded in size by the cutoff of the site, this is false. This file
proves it.

Take `X = B = Spec ℤ`, the terminal object of the site over `Spec ℤ`, with `f = 𝟙`,
`G = 𝒪_X` and `F = ⊕_{i ∈ I} 𝒪_X` the free module on a set `I` of cardinality the cutoff `κ`.
Then `f` is of finite presentation and `G` is invertible, hence of finite presentation, flat
over `B` and with support proper over `B`, and `F` is quasi-coherent. If `Hom(F, G)` were an
algebraic space `H` affine over `B`, then `H` would be represented by an affine scheme `W` of the
site, because `B` is itself affine. Its value at the test scheme `B` is then the set of morphisms
`Spec ℤ ⟶ W`, which injects into the set of maps `Γ(W) → ℤ`, of cardinality `< κ` because
`κ` is a strong limit and both rings have fewer than `κ` elements. But the value of `Hom(F, G)`
at `B` is `Hom(⊕_I 𝒪, 𝒪)`, which contains the `2 ^ κ > κ` homomorphisms that are the identity
on the summands indexed by a subset `J ⊆ I` and zero on the others.

## Main definitions

* `AlgebraicGeometry.Space.cutoffFreeBaseObject`: `Spec ℤ`, the terminal object of the site over
  `Spec ℤ`.
* `AlgebraicGeometry.Space.freeOfCutoffHomSituation`: the situation
  `(𝟙 : Spec ℤ ⟶ Spec ℤ, ⊕_{i ∈ I} 𝒪, 𝒪)` with `#I` the cutoff of the site.

## Main results

* `AlgebraicGeometry.Space.not_isAffineAlgebraicSpaceOverBase_freeOfCutoffHomSituation`: its
  relative Hom functor is not an algebraic space affine over the base.
* `AlgebraicGeometry.Space.exists_homSituation_not_isAffineAlgebraicSpaceOverBase`: on every big
  fppf site the first assertion of Stacks 08K6 fails for some quasi-coherent `F`, all other
  hypotheses of 08K6 holding.

## References

* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})

/-- `Spec ℤ`, the terminal object of the big fppf site over `Spec ℤ`. -/
abbrev cutoffFreeBaseObject : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal :=
  Over.mk (𝟙 (B.obj B.contains_terminal))

/-- `Spec ℤ`, the terminal object of the site over `Spec ℤ`, as an algebraic space. -/
abbrev cutoffFreeBaseSpace : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal :=
  (schemeSpaceFunctor B _ _).obj (cutoffFreeBaseObject B)

/-- An index set whose cardinality is the cutoff of the site. -/
abbrev CutoffIndex : Type u := B.cutoff.out

/-- The structure sheaf of `Spec ℤ`, read as a module over itself, is invertible. -/
theorem isInvertibleModule_unit_cutoffFreeBaseSpace :
    IsInvertibleModule (cutoffFreeBaseSpace B) (SheafOfModules.unit _) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- The structure sheaf of `Spec ℤ` is of finite presentation. -/
theorem isFinitePresentationOnSite_unit_cutoffFreeBaseSpace :
    (SheafOfModules.unit _ : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_of_isInvertibleModule _ (isInvertibleModule_unit_cutoffFreeBaseSpace B)

/-- The structure sheaf of `Spec ℤ` is quasi-coherent. -/
theorem isQuasicoherentOnSite_unit_cutoffFreeBaseSpace :
    (SheafOfModules.unit _ : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2).IsQuasicoherentOnSite :=
  have := isFinitePresentationOnSite_unit_cutoffFreeBaseSpace B
  SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _

/-- A free module on `Spec ℤ` is quasi-coherent: it is a direct sum of copies of the structure
sheaf (Stacks 03M1). -/
theorem isQuasicoherentOnSite_free_cutoffFreeBaseSpace (I : Type u) :
    (SheafOfModules.free I : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit_cofan B _ _ _ _ (SheafOfModules.freeCofan I)
    (SheafOfModules.isColimitFreeCofan I) fun _ => isQuasicoherentOnSite_unit_cutoffFreeBaseSpace B

/-- **The situation `(𝟙 : Spec ℤ ⟶ Spec ℤ, ⊕_{i ∈ I} 𝒪, 𝒪)` with `#I` the cutoff of the site.**
-/
def freeOfCutoffHomSituation : HomSituation B (⊤_ Scheme.{u}) B.contains_terminal where
  X := cutoffFreeBaseSpace B
  base := cutoffFreeBaseSpace B
  f := 𝟙 _
  F := SheafOfModules.free (CutoffIndex B)
  G := SheafOfModules.unit _
  quasicoherent_F := isQuasicoherentOnSite_free_cutoffFreeBaseSpace B _
  quasicoherent_G := isQuasicoherentOnSite_unit_cutoffFreeBaseSpace B

/-- The morphism of the situation is of finite presentation: it is an identity. -/
theorem isFinitePresentation_freeOfCutoffHomSituation :
    IsFinitePresentation B _ _ (freeOfCutoffHomSituation B).f.hom :=
  ⟨isLocallyOfFinitePresentation_id B _ _ (cutoffFreeBaseSpace B).2,
    isQuasiCompact_of_isIso B _ _ (𝟙 _),
    isQuasiSeparated_of_isSeparated B _ _ (isSeparated_of_isIso B _ _ (𝟙 _))⟩

/-- The target module of the situation is of finite presentation. -/
theorem isFinitePresentationOnSite_freeOfCutoffHomSituation_G :
    (freeOfCutoffHomSituation B).G.IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_unit_cutoffFreeBaseSpace B

/-- The target module of the situation is flat over the base. -/
theorem isFlatOver_freeOfCutoffHomSituation_G :
    IsFlatOver B _ _ (freeOfCutoffHomSituation B).X.2 (freeOfCutoffHomSituation B).f.hom
      (freeOfCutoffHomSituation B).G :=
  isFlatOver_of_isInvertibleModule (𝟙 _) _ (isFlat_id B _ _ (cutoffFreeBaseSpace B).2)
    (isInvertibleModule_unit_cutoffFreeBaseSpace B)

/-- The target module of the situation has support proper over the base. -/
theorem hasProperSupport_freeOfCutoffHomSituation_G :
    HasProperSupport B _ _ (freeOfCutoffHomSituation B).X.2 (freeOfCutoffHomSituation B).base.2
      (freeOfCutoffHomSituation B).f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ _
        (isFinitePresentation_freeOfCutoffHomSituation B).1)
      ((SheafOfModules.toSheaf _).obj (freeOfCutoffHomSituation B).G) :=
  isProperOver_supportOfSheaf_of_isInvertibleModule (𝟙 _) _ _
    (isProper_of_isIso B _ _ (𝟙 _)) (isInvertibleModule_unit_cutoffFreeBaseSpace B)

/-! ### The relative Hom functor is not an algebraic space -/

/-- `Spec ℤ` is nonempty. -/
instance nonempty_terminalScheme : Nonempty (⊤_ Scheme.{u}) :=
  ⟨(terminal.from (Spec (.of (ULift.{u} ℤ)))).base (Nonempty.some inferInstance)⟩

/-- The identity of the structure sheaf of `Spec ℤ` is not zero: its value on the identity chart
is the identity of the nonzero ring `Γ(Spec ℤ)`. -/
theorem id_unit_ne_zero_cutoffFreeBaseSpace :
    (𝟙 (SheafOfModules.unit _ : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2)) ≠ 0 := by
  intro h
  let U := idChart B _ B.contains_terminal (cutoffFreeBaseObject B)
  let x : ((SheafOfModules.unit _ : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2).val.obj (op U) : Type u) := (1 : Γ(⊤_ Scheme.{u}, ⊤))
  have : Nonempty (⊤ : (⊤_ Scheme.{u}).Opens) :=
    ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  exact one_ne_zero (α := Γ(⊤_ Scheme.{u}, ⊤)) (congrArg (fun φ => (φ.val.app (op U)).hom x) h)

variable {B} in
/-- The homomorphism `⊕_{i ∈ I} 𝒪 ⟶ 𝒪` which is the identity on the summands indexed by `J`
and zero on the others. -/
def indicatorHom {I : Type u} (J : Set I) :
    (SheafOfModules.free I : Modules.{u, u} B _ _ (cutoffFreeBaseSpace B).1
      (cutoffFreeBaseSpace B).2) ⟶ SheafOfModules.unit _ :=
  (SheafOfModules.freeHomEquiv _).symm fun i =>
    (SheafOfModules.unit _).unitHomEquiv (by classical exact if i ∈ J then 𝟙 _ else 0)

/-- Distinct subsets give distinct indicator homomorphisms. -/
theorem indicatorHom_injective (I : Type u) :
    Function.Injective (indicatorHom (B := B) (I := I)) := by
  refine (SheafOfModules.freeHomEquiv _).symm.injective.comp ?_
  intro J J' h
  refine Set.ext fun i => ?_
  have h2 := (SheafOfModules.unit _).unitHomEquiv.injective (congrFun h i)
  have hne := id_unit_ne_zero_cutoffFreeBaseSpace B
  by_cases hJ : i ∈ J <;> by_cases hJ' : i ∈ J' <;> simp only [hJ, hJ', ite_true, ite_false] at h2 ⊢
  exacts [(hne h2).elim, (hne h2.symm).elim]

/-- The test scheme `Spec ℤ` over the base, by the identity. -/
abbrev freeOfCutoffTestScheme : (freeOfCutoffHomSituation B).SchemesOver :=
  CostructuredArrow.mk (Y := cutoffFreeBaseObject B) (𝟙 (cutoffFreeBaseSpace B))

/-- The projection `X_T ⟶ X` at the identity test scheme is an isomorphism. -/
instance isIso_projection_freeOfCutoffTestScheme :
    IsIso ((freeOfCutoffHomSituation B).projection (freeOfCutoffTestScheme B)) :=
  (AlgebraicSpaces.isPullback_fiberProduct B _ _ (𝟙 (cutoffFreeBaseSpace B))
    (𝟙 (cutoffFreeBaseSpace B))).isIso_fst_of_isIso

/-- There are at least `2 ^ #I` homomorphisms `F_T ⟶ G_T` at the identity test scheme: the
inverse images of the indicator homomorphisms, along the projection `X_T ⟶ X`, which is an
isomorphism. -/
theorem injective_homAt_freeOfCutoffTestScheme :
    ∃ g : Set (CutoffIndex B) → (freeOfCutoffHomSituation B).homAt (freeOfCutoffTestScheme B),
      Function.Injective g := by
  let P := modulePullback B _ _
    ((freeOfCutoffHomSituation B).projection (freeOfCutoffTestScheme B))
  have : P.Faithful := faithful_modulePullback_of_isIso _
  exact ⟨fun J => P.map (indicatorHom J),
    fun _ _ h => indicatorHom_injective B _ (P.map_injective h)⟩

/-- `Spec ℤ`, as an object of the big affine fppf site over `Spec ℤ`. -/
abbrev cutoffFreeBaseAffineObject : BigAffineFppf B (⊤_ Scheme.{u}) B.contains_terminal :=
  ⟨cutoffFreeBaseObject B, inferInstanceAs (IsAffine (⊤_ Scheme.{u}))⟩

/-- **The relative Hom functor out of a free module of rank the cutoff is not an algebraic space
affine over the base.** For `X = B = Spec ℤ`, `f = 𝟙`, `G = 𝒪` and `F = ⊕_{i ∈ I} 𝒪` with `#I`
the cutoff `κ` of the site, an algebraic space `H` affine over `Spec ℤ` representing `Hom(F, G)`
would be an affine scheme `W` of the site, and `Hom(F, G)(Spec ℤ)` would inject into the maps
`Γ(W) → Γ(Spec ℤ)`, of which there are fewer than `κ` because `κ` is a strong limit; but
`Hom(F, G)(Spec ℤ)` has at least `2 ^ κ` elements. -/
theorem not_isAffineAlgebraicSpaceOverBase_freeOfCutoffHomSituation
    (hc : ModulePushforwardCoherence B _ B.contains_terminal) :
    ¬ (freeOfCutoffHomSituation B).IsAffineAlgebraicSpaceOverBase hc := by
  rintro ⟨H, p, hp, ⟨c⟩⟩
  obtain ⟨g, hg⟩ := injective_homAt_freeOfCutoffTestScheme B
  let T₀ := freeOfCutoffTestScheme B
  let Z := cutoffFreeBaseObject B
  obtain ⟨W, p', q, hpb⟩ := hp (cutoffFreeBaseAffineObject B) (𝟙 _)
  have : IsIso p' := hpb.isIso_fst_of_isIso (IsIso.id _)
  let W' := (BigAffineFppf.inclusion B _ _).obj W
  have : IsAffine ((BigFppfOver.toScheme B _ _).obj W') := W.property
  have : IsAffine ((BigFppfOver.toScheme B _ _).obj Z) :=
    inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  -- the value of `Hom(F, G)` at `T₀` is the points of `H` over `T₀`
  let e₁ : (freeOfCutoffHomSituation B).homAt T₀ ≃ ULift.{u + 1} (spacePointsOverObj p T₀) :=
    (c.app (op T₀)).symm.toEquiv
  -- the sections of `H` over `Spec ℤ` are the morphisms `Spec ℤ ⟶ W` of the site
  let e₂ : H.1.obj (op Z) ≃ (Z ⟶ W') := ((asIso p').app (op Z)).symm.toEquiv
  -- a morphism `Spec ℤ ⟶ W` of schemes, with `W` affine, is determined by its map on global
  -- sections
  let φ : (Z ⟶ W') → (Γ((BigFppfOver.toScheme B _ _).obj W', ⊤) →
      Γ((BigFppfOver.toScheme B _ _).obj Z, ⊤)) :=
    fun m => ((BigFppfOver.toScheme B _ _).map m).appTop.hom
  have hφ : Function.Injective φ := fun _ _ h =>
    (BigFppfOver.toScheme B _ _).map_injective
      (ext_of_isAffine (CommRingCat.hom_ext (RingHom.coe_inj h)))
  let k : Set (CutoffIndex B) → (Γ((BigFppfOver.toScheme B _ _).obj W', ⊤) →
      Γ((BigFppfOver.toScheme B _ _).obj Z, ⊤)) :=
    fun J => φ (e₂ (e₁ (g J)).down.1)
  have hk : Function.Injective k := fun _ _ h =>
    hg (e₁.injective (ULift.ext (Subtype.ext (e₂.injective (hφ h)))))
  have hle := mk_le_of_injective hk
  rw [mk_set, ← power_def, mk_out] at hle
  have hsections : ∀ (V : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)
      [IsAffine ((BigFppfOver.toScheme B _ _).obj V)],
      #Γ((BigFppfOver.toScheme B _ _).obj V, ⊤) < B.cutoff := fun V =>
    (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩).trans_lt V.left.property
  exact (hle.trans_lt (power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit (hsections Z) (hsections W'))).not_ge (cantor B.cutoff).le

/-- **The first assertion of Stacks 08K6, for an arbitrary quasi-coherent `F`, fails on every big
fppf site.** There is a relative Hom situation over `Spec ℤ` with `f` of finite presentation and
`G` of finite presentation, flat over the base and with support proper over the base, whose
relative Hom functor is not an algebraic space affine over the base: the situation
`(𝟙 : Spec ℤ ⟶ Spec ℤ, ⊕_{i ∈ I} 𝒪, 𝒪)` with `#I` the cutoff of the site. -/
theorem exists_homSituation_not_isAffineAlgebraicSpaceOverBase :
    ∃ (s : HomSituation B (⊤_ Scheme.{u}) B.contains_terminal)
      (hfp : IsFinitePresentation B _ _ s.f.hom),
      s.G.IsFinitePresentationOnSite ∧ IsFlatOver B _ _ s.X.2 s.f.hom s.G ∧
      HasProperSupport B _ _ s.X.2 s.base.2 s.f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ _ hfp.1)
        ((SheafOfModules.toSheaf _).obj s.G) ∧
      ∀ hc : ModulePushforwardCoherence B _ B.contains_terminal,
        ¬ s.IsAffineAlgebraicSpaceOverBase hc :=
  ⟨freeOfCutoffHomSituation B, isFinitePresentation_freeOfCutoffHomSituation B,
    isFinitePresentationOnSite_freeOfCutoffHomSituation_G B,
    isFlatOver_freeOfCutoffHomSituation_G B, hasProperSupport_freeOfCutoffHomSituation_G B,
    not_isAffineAlgebraicSpaceOverBase_freeOfCutoffHomSituation B⟩

/-- **The first assertion of Stacks 08K6, as written, is false on every big fppf site.** The
statement "in Situation 08JT, if `f` is of finite presentation and `G` is of finite presentation,
flat over `B`, with support proper over `B`, then `Hom(F, G)` is an algebraic space affine over
`B`", quantified over all situations (so over all quasi-coherent `F`), does not hold. -/
theorem not_forall_isAffineAlgebraicSpaceOverBase :
    ¬ ∀ (S : Scheme.{u}) (hS : B.Contains S) (s : HomSituation B S hS)
      (hc : ModulePushforwardCoherence B S hS) (hfp : IsFinitePresentation B S hS s.f.hom),
      s.G.IsFinitePresentationOnSite → IsFlatOver B S hS s.X.2 s.f.hom s.G →
      HasProperSupport B S hS s.X.2 s.base.2 s.f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfp.1)
        ((SheafOfModules.toSheaf _).obj s.G) →
      s.IsAffineAlgebraicSpaceOverBase hc := by
  intro h
  obtain ⟨s, hfp, hG, hflat, hsupp, hnot⟩ :=
    exists_homSituation_not_isAffineAlgebraicSpaceOverBase B
  exact hnot (modulePushforwardCoherence B _ _)
    (h _ _ s (modulePushforwardCoherence B _ _) hfp hG hflat hsupp)

end AlgebraicGeometry.Space

end
