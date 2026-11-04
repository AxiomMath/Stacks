module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveSupportClosed
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a smooth relative cycle is open and closed

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be smooth of relative dimension `r` and
let `α` be a relative `r`-cycle on `X/S`. Then the support of `α` is open and closed in `X`.
That is Lemma 0H5B, and `Stacks.Chow.isClopen_supportOfFamily_of_smoothOfRelativeDimension` is
it.

The reduction of the statement to the invariance of membership in the support along
specializations is
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen`; this file supplies
that invariance.

A specialization `x ⤳ y` in `X` is realized by the generic-to-closed specialization on the
spectrum of a discrete valuation ring `R` mapping to `X`, and the base change
`X ×_S Spec R ⟶ Spec R` — smooth of relative dimension `r` again — carries a section through
which the two points are seen. So everything reduces to a morphism `p : Y ⟶ Spec R` smooth of
relative dimension `r` with a point `a` of the generic fibre specializing to a point `b` of the
special fibre.

There `Y` is regular, being smooth over the regular ring `R`, hence normal; on a locally
Noetherian normal scheme a connected component is open and, as an open subscheme, integral. So
the connected component of `b` is an open and closed integral subscheme, and `a` lies in it
because that component is open. Restricting the family to it — which preserves both the
valuative condition and the support, by
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction` — reduces the
statement to an integral total space.

On an integral total space the generic fibre is integral as well, and smooth of relative
dimension `r` over the fraction field, so its generic point has dimension `r` while every other
point has smaller dimension. The cycle on the generic fibre is therefore concentrated at that
generic point with some coefficient `n`, and *every* point of the generic fibre lies in the
support exactly when `n ≠ 0`. The same holds on the special fibre: if `n = 0` the cycle on the
generic fibre vanishes and so does its specialization, while if `n ≠ 0` that cycle — or its
negative — is effective with a nonzero coefficient at a point whose image is the generic point
of `Y`, which specializes to every point of `Y`, so the specialized cycle is supported
everywhere on the special fibre.

## Main results

* `AlgebraicGeometry.isRegular_of_smooth_over_regular` — a scheme smooth over the spectrum of a
  regular ring is regular.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field`,
  `AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field` — a scheme
  smooth of relative dimension `n` over a field has dimension `n`, at every point and globally.
* `Stacks.Chow.relativeDimension_genericPoint_of_smoothOfRelativeDimension`,
  `Stacks.Chow.fiberPointDimension_genericPoint_of_smoothOfRelativeDimension` — the relative
  dimension of such a scheme, and of an integral fibre of a morphism smooth of relative
  dimension `r`, at its generic point.
* `Stacks.Chow.isIntegral_of_connectedSpace_of_isNormal` — a connected locally Noetherian normal
  scheme is integral.
* `Stacks.Chow.isOpen_connectedComponent_of_isLocallyNoetherian`,
  `Stacks.Chow.irreducibleComponent_eq_connectedComponent_of_isIntegral` — connected components
  of a locally Noetherian scheme are open, and are the irreducible components when they are
  integral.
* `Stacks.Chow.tsupport_fiberCycleRestrict`,
  `Stacks.Chow.mem_supportOfFamily_fiberCycleRestrict_iff` — restriction to an open subscheme of
  the source intersects supports with that open subscheme.
* `Stacks.Chow.isClopen_supportOfFamily_of_smoothOfRelativeDimension` — **Lemma 0H5B**.

## Implementation notes

`AlgebraicGeometry.isRegular_of_smooth_over_regular` and
`Stacks.Chow.isIntegral_of_connectedSpace_of_isNormal` are the versions over a general affine
regular base of `AlgebraicGeometry.isRegular_of_smooth_over_field` and of the smooth-over-a-field
argument inlined in `Stacks.Chow.isIntegral_of_connectedSpace_of_smooth`; the proofs are the same
and the field versions are left where they are.

The codomain of `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` is `Spec κ(s)` with
`κ(s)` a `CommRingCat`, while the lemmas about schemes over a field are stated for `Spec (.of k)`
with `k` a type; the two agree definitionally but not up to the reducible unfolding that instance
search uses. Instances for the fibre morphism are therefore passed explicitly rather than
synthesized.

`[LocallyOfFiniteType f]` appears in the hypotheses of the main theorem although it follows from
smoothness: `Stacks.Chow.FamilyOfCycles f r` needs it to be stated at all, so it has to be an
instance argument of the statement rather than a consequence drawn inside the proof.

The source proves the stronger statement that the fibrewise coefficient function `x ↦ n_x` is
locally constant, and in the final step shrinks the total space, using the openness of the union
of the connected components of the fibres meeting a section (Section 37.29, Lemma 055R), so that
the fibres become connected. The argument here needs no such input: over a discrete valuation
ring the total space of a smooth morphism is regular, hence normal, so its connected components
are already open and closed and are integral as open subschemes.

## References

* [Stacks Project, Lemma 0H5B](https://stacks.math.columbia.edu/tag/0H5B)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Lemma 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 056S.** A scheme smooth over the spectrum of a regular ring is
regular: on an affine open of the source the sections form a smooth algebra over the global
sections of the base, which is a regular ring, and a smooth algebra over a regular ring is
regular. -/
theorem isRegular_of_smooth_over_regular {R : Type u} [CommRing R] [IsRegularRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] : IsRegular X := by
  intro x
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
    rw [← Opens.mem_iSup, iSup_affineOpens_eq_top]
    trivial
  refine ⟨U, hxU, ?_⟩
  let : IsRegularRing Γ(Spec (.of R), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let φ := (f.appLE ⊤ U.1 (le_top : U.1 ≤ f ⁻¹ᵁ ⊤)).hom
  let : Algebra Γ(Spec (.of R), ⊤) Γ(X, U.1) := φ.toAlgebra
  let : Algebra.Smooth Γ(Spec (.of R), ⊤) Γ(X, U.1) :=
    (f.smooth_appLE (isAffineOpen_top _) U.2 le_top).toAlgebra
  exact Algebra.isRegularRing_of_smooth Γ(Spec (.of R), ⊤) Γ(X, U.1)

/-- **Stacks Project, Tag 0B9D.** A scheme smooth of relative dimension `n` over a field has
topological Krull dimension `n` at every point: the structure morphism has a single fibre,
which is the scheme itself, and the fibre dimension of a morphism smooth of relative dimension
`n` is `n` at every point. -/
theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}} (n : ℕ) (p : Y ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n p] (y : Y) :
    topologicalKrullDimAt Y y = (n : WithBot ℕ∞) := by
  have hfiber := fiberDimensionAt_eq_of_smoothOfRelativeDimension p n y
  have hpre : p ⁻¹' {p y} = Set.univ := by
    ext z
    change p z = p y ↔ True
    exact ⟨fun _ ↦ trivial, fun _ ↦ Subsingleton.elim _ _⟩
  let e : p.fiber (p y) ≃ₜ Y :=
    (p.fiberHomeo (p y)).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ Y))
  have he : e (p.asFiber y) = y := by
    simp [e, Scheme.Hom.asFiber]
    rfl
  have hdim : topologicalKrullDimAt (p.fiber (p y)) (p.asFiber y) =
      topologicalKrullDimAt Y y := by
    simpa only [he] using topologicalKrullDimAt_eq_of_homeomorph e (p.asFiber y)
  rw [← hdim, hfiber]

/-- A nonempty scheme smooth of relative dimension `n` over a field has topological Krull
dimension `n`: its dimension at every point is `n`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}} [Nonempty Y] (n : ℕ) (p : Y ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n p] : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
  have hloc (y : Y) : localKrullDim Y y = (n : WithBot ℕ∞) := by
    rw [← topologicalKrullDimAt_eq_localKrullDim]
    exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field n p y
  rw [topologicalKrullDim_eq_iSup_localKrullDim, iSup_congr hloc, iSup_const]

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The relative dimension of a smooth scheme at its generic point -/

/-- Precomposing a morphism smooth of relative dimension `r` with an open immersion keeps the
relative dimension `r`. -/
private theorem smoothOfRelativeDimension_comp_of_isOpenImmersion {V Y Z : Scheme.{u}}
    (j : V ⟶ Y) (p : Y ⟶ Z) (r : ℕ) [IsOpenImmersion j] [SmoothOfRelativeDimension r p] :
    SmoothOfRelativeDimension r (j ≫ p) := by
  have h0 : SmoothOfRelativeDimension (0 + r) (j ≫ p) := inferInstance
  rwa [Nat.zero_add] at h0

/-- The base change projection `pullback.snd f g` of a morphism smooth of relative dimension `r`
is again smooth of relative dimension `r`. -/
private theorem smoothOfRelativeDimension_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (r : ℕ) [SmoothOfRelativeDimension r f] :
    SmoothOfRelativeDimension r (pullback.snd f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := r)).of_isPullback
    (IsPullback.of_hasPullback f g) inferInstance

/-- The relative dimension of an integral scheme smooth of relative dimension `n` over a field,
at its generic point, is `n`: the dimension of such a scheme is `n`, and the relative dimension
at the generic point of an integral scheme over a field is its dimension. -/
theorem relativeDimension_genericPoint_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral Y] (n : ℕ) (p : Y ⟶ Spec (.of k))
    [SmoothOfRelativeDimension n p] :
    relativeDimension (fieldChowSituation k).dimensionFunction p (genericPoint Y) = (n : ℤ) :=
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  relativeDimension_fieldChowSituation_genericPoint p
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n p)

/-- The dimension of the generic point of an integral scheme-theoretic fibre of a morphism
smooth of relative dimension `r` is `r`: the fibre is smooth of relative dimension `r` over the
residue field of its base point. -/
theorem fiberPointDimension_genericPoint_of_smoothOfRelativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) [SmoothOfRelativeDimension r f] (s : S)
    [AlgebraicGeometry.IsIntegral (f.fiber s)] :
    fiberPointDimension f s (genericPoint (f.fiber s)) = (r : ℤ) := by
  have hsm : SmoothOfRelativeDimension r (f.fiberToSpecResidueField s) :=
    smoothOfRelativeDimension_pullback_snd f (S.fromSpecResidueField s) r
  exact @relativeDimension_genericPoint_of_smoothOfRelativeDimension ↥(S.residueField s)
    inferInstance (f.fiber s) inferInstance r (f.fiberToSpecResidueField s) hsm

/-! ### Connected components of a normal locally Noetherian scheme -/

/-- A connected locally Noetherian normal scheme is integral: a locally Noetherian normal
scheme is a coproduct of integral schemes, and connectedness forces the index set of that
coproduct to be a singleton. -/
theorem isIntegral_of_connectedSpace_of_isNormal {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] [ConnectedSpace Y] : IsIntegral Y := by
  classical
  obtain ⟨ι, Z, -, hZint, ⟨e⟩⟩ := (isNormal_iff_exists_iso_coproduct_integral_normal Y).mp
    (inferInstance : IsNormal Y)
  let h : Y ≃ₜ (Σ i, Z i) := e.hom.homeomorph.trans (sigmaMk Z).symm
  have huniv (i : ι) (x : Z i) : (h ⁻¹' Set.range (Sigma.mk i) : Set Y) = Set.univ :=
    (isClopen_iff.mp ⟨isClopen_range_sigmaMk.1.preimage h.continuous,
      isClopen_range_sigmaMk.2.preimage h.continuous⟩).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨h.symm ⟨i, x⟩, by simp⟩)
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  have hfst (i : ι) (x : Z i) : (h y).1 = i := by
    obtain ⟨a, ha⟩ : h y ∈ Set.range (Sigma.mk i) := by
      rw [← Set.mem_preimage, huniv i x]; trivial
    exact (congrArg Sigma.fst ha).symm
  let _ : Nonempty ι := ⟨(h y).1⟩
  let _ : Subsingleton ι := ⟨fun i j ↦ by
    let _ := hZint i
    let _ := hZint j
    obtain ⟨xi⟩ := (inferInstance : Nonempty (Z i))
    obtain ⟨xj⟩ := (inferInstance : Nonempty (Z j))
    rw [← hfst i xi, hfst j xj]⟩
  let _ : Unique ι := uniqueOfSubsingleton (Classical.arbitrary ι)
  let _ := hZint default
  exact IsIntegral.of_isIso (e ≪≫ Limits.coproductUniqueIso Z).inv

/-- The connected component of a point of a locally Noetherian scheme is open: a locally
Noetherian space is locally connected. -/
@[ega "I 6.1.9" "special case",
  sga "1 IX 5.1" "more general",
  sga "3 VIA 2.3" "partial",
  sga "3 X 5.11.0",
  sga "3 X 6.2" "partial"]
theorem isOpen_connectedComponent_of_isLocallyNoetherian {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (y : Y) : IsOpen (connectedComponent y) :=
  let _ : LocallyConnectedSpace Y := IsLocallyNoetherianSpace.locallyConnectedSpace _
    (isLocallyNoetherianSpace_of_isLocallyNoetherian Y)
  isOpen_connectedComponent

/-- On a locally Noetherian scheme all of whose open subschemes supported on connected
components are integral, the irreducible component through a point is its connected component.
One inclusion holds because an irreducible set is connected; the other because the connected
component is irreducible and so cannot properly contain an irreducible component. -/
@[ega "I 6.1.10" "(c) ⇒ (b), special case"]
theorem irreducibleComponent_eq_connectedComponent_of_isIntegral {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (y : Y)
    (hint : ∀ hopen : IsOpen (connectedComponent y),
      IsIntegral ((⟨connectedComponent y, hopen⟩ : Y.Opens) : Scheme.{u})) :
    irreducibleComponent y = connectedComponent y := by
  have hopen : IsOpen (connectedComponent y) :=
    isOpen_connectedComponent_of_isLocallyNoetherian y
  let _ := hint hopen
  have hirr : IsIrreducible (connectedComponent y) := isIrreducible_iff_irreducibleSpace.mpr
    (inferInstance : IrreducibleSpace ((⟨connectedComponent y, hopen⟩ : Y.Opens) : Scheme.{u}))
  have hsub : irreducibleComponent y ⊆ connectedComponent y :=
    isIrreducible_irreducibleComponent.isConnected.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  exact subset_antisymm hsub ((irreducibleComponent_mem_irreducibleComponents y).2 hirr hsub)

/-! ### The support of a family restricted to an open subscheme of the source -/

/-- The support of a cycle restricted along an open immersion of fibres is the inverse image of
its support: the coefficients are restricted along an open map, which commutes with closure on
inverse images. -/
@[ega "IV 21.6.3" "special case"]
theorem tsupport_fiberCycleRestrict {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU)
    (s : S) (r : ℕ) (c : FiberCycleGroup f s r) :
    tsupport (fiberCycleRestrict f fU j h s r c : AlgebraicCycle (fU.fiber s) ℤ) =
      fiberRestrict f fU j h s ⁻¹' tsupport (c : AlgebraicCycle (f.fiber s) ℤ) := by
  let : IsOpenImmersion (fiberRestrict f fU j h s) := isOpenImmersion_fiberRestrict f fU j h s
  have hopen : IsOpenMap (fiberRestrict f fU j h s) :=
    (fiberRestrict f fU j h s).isOpenEmbedding.isOpenMap
  have hsupp : Function.support
      (fiberCycleRestrict f fU j h s r c : AlgebraicCycle (fU.fiber s) ℤ) =
      fiberRestrict f fU j h s ⁻¹' Function.support (c : AlgebraicCycle (f.fiber s) ℤ) := rfl
  rw [tsupport, hsupp,
    ← hopen.preimage_closure_eq_closure_preimage (fiberRestrict f fU j h s).continuous]
  rfl

/-- A point of an open subscheme of the source lies in the support of a restricted family
exactly when its image lies in the support of the original family. -/
theorem mem_supportOfFamily_fiberCycleRestrict_iff {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ) (α : FamilyOfCycles f r) (s : S)
    (y : fU.fiber s) (u : U) (hu : fU.fiberι s y = u) :
    u ∈ supportOfFamily fU (fun t ↦ fiberCycleRestrict f fU j h t r (α t)) ↔
      j u ∈ supportOfFamily f α := by
  subst hu
  rw [fiberι_mem_supportOfFamily_iff fU r _ _ y, tsupport_fiberCycleRestrict,
    Set.mem_preimage, ← fiberι_mem_supportOfFamily_iff f r α _ (fiberRestrict f fU j h _ y),
    ← Scheme.Hom.comp_apply, fiberRestrict_fiberι, Scheme.Hom.comp_apply]

/-! ### The specialization step over a discrete valuation ring -/

/-- Over the spectrum of a discrete valuation ring, on an *integral* total space smooth of
relative dimension `r`, a family of `r`-cycles satisfying the valuative condition has the same
support behaviour on the two fibres: a point of the generic fibre lies in the support if and
only if a point of the special fibre does.

Indeed the generic fibre is integral of dimension `r`, so the cycle on it is concentrated at
its generic point, with some coefficient `n`; every point of the generic fibre lies in the
support exactly when `n ≠ 0`. On the special fibre the cycle is the specialization of that one:
if `n = 0` the cycle on the generic fibre vanishes and so does its specialization, while if
`n ≠ 0` the cycle — or its negative — is effective with a nonzero coefficient at a point whose
image is the generic point of the total space, which specializes to every point. -/
private theorem mem_supportOfFamily_iff_of_isIntegral_over_dvr {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {W : Scheme.{u}} (q : W ⟶ Spec (.of R))
    [LocallyOfFiniteType q] (r : ℕ) [SmoothOfRelativeDimension r q]
    [AlgebraicGeometry.IsIntegral W] (γ : FamilyOfCycles q r)
    (hsp : specializationCycle q r (γ (genericPoint (Spec (.of R)))) =
      γ (IsLocalRing.closedPoint R))
    {a b : W} (ha : q a = genericPoint (Spec (.of R)))
    (hb : q b = IsLocalRing.closedPoint R) :
    (a ∈ supportOfFamily q γ ↔ b ∈ supportOfFamily q γ) := by
  classical
  let : Smooth q := SmoothOfRelativeDimension.smooth r q
  -- the point of the generic fibre lying over the generic point of `W`
  obtain ⟨ξ, hξ⟩ := (q.range_fiberι (genericPoint (Spec (.of R)))).symm.subset
    (base_genericPoint_eq_genericPoint q)
  have hclos : closure ({ξ} : Set (q.fiber (genericPoint (Spec (.of R))))) = Set.univ :=
    closure_eq_univ_of_fiberι_eq_genericPoint q ξ hξ
  have hirrtop : IsIrreducible (⊤ : Set (q.fiber (genericPoint (Spec (.of R))))) := by
    rw [Set.top_eq_univ, ← hclos]
    exact isIrreducible_singleton.closure
  let hirr : IrreducibleSpace (q.fiber (genericPoint (Spec (.of R)))) :=
    (irreducibleSpace_def _).2 hirrtop
  -- the generic fibre is smooth of relative dimension `r` over the residue field
  have hlft : LocallyOfFiniteType (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) := by
    change LocallyOfFiniteType
      (pullback.snd q (Scheme.fromSpecResidueField _ (genericPoint (Spec (.of R)))))
    infer_instance
  have hsm : Smooth (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) := by
    change Smooth (pullback.snd q (Scheme.fromSpecResidueField _ (genericPoint (Spec (.of R)))))
    infer_instance
  let : IsLocallyNoetherian (q.fiber (genericPoint (Spec (.of R)))) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) hlft inferInstance
  let : IsNormal (q.fiber (genericPoint (Spec (.of R)))) := isNormal_of_isRegular _
    (@isRegular_of_smooth_over_field _ inferInstance _
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) hsm)
  let : AlgebraicGeometry.IsIntegral (q.fiber (genericPoint (Spec (.of R)))) :=
    isIntegral_of_connectedSpace_of_isNormal
  have hξgen : ξ = genericPoint (q.fiber (genericPoint (Spec (.of R)))) :=
    IsGenericPoint.eq hclos (genericPoint_spec _)
  have hdim : relativeDimension (fieldChowSituation _).dimensionFunction
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R))))
      (genericPoint (q.fiber (genericPoint (Spec (.of R))))) = (r : ℤ) :=
    fiberPointDimension_genericPoint_of_smoothOfRelativeDimension q r _
  have hlt : ∀ x : q.fiber (genericPoint (Spec (.of R))),
      x ≠ genericPoint (q.fiber (genericPoint (Spec (.of R)))) →
      relativeDimension (fieldChowSituation _).dimensionFunction
        (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) x < (r : ℤ) := by
    intro x hx
    have h := @relativeDimension_lt_of_ne_genericPoint (fieldChowSituation _) _ hirr
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) hlft x hx
    rwa [hdim] at h
  -- the coefficient at the generic point of the generic fibre
  set n : ℤ := (γ (genericPoint (Spec (.of R))) :
    AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ)
    (genericPoint (q.fiber (genericPoint (Spec (.of R))))) with hn
  have hvanish : ∀ x : q.fiber (genericPoint (Spec (.of R))),
      x ≠ genericPoint (q.fiber (genericPoint (Spec (.of R)))) →
      (γ (genericPoint (Spec (.of R))) :
        AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ) x = 0 := by
    intro x hx
    by_contra hne
    exact absurd ((@mem_cyclesOfDimension_iff_forall_point (fieldChowSituation _) _
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) hlft (r : ℤ) _).mp
      (γ (genericPoint (Spec (.of R)))).2 x hne ▸ hlt x hx) (lt_irrefl _)
  -- every point of the generic fibre is in the support exactly when `n ≠ 0`
  have hA : a ∈ supportOfFamily q γ ↔ n ≠ 0 := by
    obtain ⟨za, hza⟩ := (q.range_fiberι (genericPoint (Spec (.of R)))).symm.subset ha
    rw [← hza, fiberι_mem_supportOfFamily_iff q r γ _ za]
    exact @mem_tsupport_iff_genericPoint_coeff_ne_zero (fieldChowSituation _) _ _
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) hlft (r : ℤ) hdim hlt _ za
  -- and so is every point of the special fibre
  have hB : b ∈ supportOfFamily q γ ↔ n ≠ 0 := by
    obtain ⟨zb, hzb⟩ := (q.range_fiberι (IsLocalRing.closedPoint R)).symm.subset hb
    rw [← hzb, fiberι_mem_supportOfFamily_iff q r γ _ zb, ← hsp]
    have key : ∀ c : FiberCycleGroup q (genericPoint (Spec (.of R))) r,
        (∀ x, 0 ≤ (c : AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ) x) →
        (c : AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ)
          (genericPoint (q.fiber (genericPoint (Spec (.of R))))) ≠ 0 →
        zb ∈ tsupport (specializationCycle q r c :
          AlgebraicCycle (q.fiber (IsLocalRing.closedPoint R)) ℤ) := by
      intro c heff hne
      refine mem_tsupport_specializationCycle_of_specializes q r c heff hne zb ?_
      rw [← hξgen, hξ]
      exact genericPoint_specializes _
    refine ⟨fun hmem hzero ↦ ?_, fun hne ↦ ?_⟩
    · have hγzero : γ (genericPoint (Spec (.of R))) = 0 := by
        refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun x ↦ ?_
        by_cases hx : x = genericPoint (q.fiber (genericPoint (Spec (.of R))))
        · rwa [hx]
        · exact hvanish x hx
      rw [hγzero, specializationCycle_zero] at hmem
      simp at hmem
    · rcases le_or_gt 0 n with h0 | h0
      · refine key _ (fun x ↦ ?_) hne
        by_cases hx : x = genericPoint (q.fiber (genericPoint (Spec (.of R))))
        · rw [hx]
          exact h0
        · rw [hvanish x hx]
      · have hc : ∀ x, ((-(γ (genericPoint (Spec (.of R)))) :
            FiberCycleGroup q (genericPoint (Spec (.of R))) r) :
            AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ) x =
            -((γ (genericPoint (Spec (.of R))) :
              AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ) x) := fun _ ↦ rfl
        have heff : ∀ x, 0 ≤ ((-(γ (genericPoint (Spec (.of R)))) :
            FiberCycleGroup q (genericPoint (Spec (.of R))) r) :
            AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ) x := by
          intro x
          rw [hc x]
          by_cases hx : x = genericPoint (q.fiber (genericPoint (Spec (.of R))))
          · rw [hx]
            exact neg_nonneg.2 h0.le
          · rw [hvanish x hx, neg_zero]
        have hne' : ((-(γ (genericPoint (Spec (.of R)))) :
            FiberCycleGroup q (genericPoint (Spec (.of R))) r) :
            AlgebraicCycle (q.fiber (genericPoint (Spec (.of R)))) ℤ)
            (genericPoint (q.fiber (genericPoint (Spec (.of R))))) ≠ 0 := by
          rw [hc]
          simpa using hne
        have hmem := key _ heff hne'
        rw [← specializationCycleHom_apply, map_neg, specializationCycleHom_apply] at hmem
        simpa [tsupport] using hmem
  rw [hA, hB]

/-- Reduction of the specialization step to an integral open piece: if both points lie in the
image of an open immersion `j : V ⟶ Y` with `V` integral, then they lie in the support of a
family satisfying the valuative condition at the same time, because the restricted family
satisfies the valuative condition on the integral `V`. -/
private theorem mem_supportOfFamily_iff_of_isIntegral_piece_over_dvr {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (r : ℕ) [SmoothOfRelativeDimension r p] (β : FamilyOfCycles p r)
    (hsp : specializationCycle p r (β (genericPoint (Spec (.of R)))) =
      β (IsLocalRing.closedPoint R))
    {V : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j] [AlgebraicGeometry.IsIntegral V]
    {a b : Y} {a' b' : V} (ha' : j a' = a) (hb' : j b' = b)
    (ha : p a = genericPoint (Spec (.of R))) (hb : p b = IsLocalRing.closedPoint R) :
    (a ∈ supportOfFamily p β ↔ b ∈ supportOfFamily p β) := by
  let : SmoothOfRelativeDimension r (j ≫ p) :=
    smoothOfRelativeDimension_comp_of_isOpenImmersion j p r
  let : Smooth (j ≫ p) := SmoothOfRelativeDimension.smooth r _
  let : LocallyOfFiniteType (j ≫ p) := inferInstance
  have hbasea : (j ≫ p) a' = genericPoint (Spec (.of R)) := by
    rw [Scheme.Hom.comp_apply, ha', ha]
  have hbaseb : (j ≫ p) b' = IsLocalRing.closedPoint R := by
    rw [Scheme.Hom.comp_apply, hb', hb]
  obtain ⟨ya, hya⟩ := ((j ≫ p).range_fiberι (genericPoint (Spec (.of R)))).symm.subset hbasea
  obtain ⟨yb, hyb⟩ := ((j ≫ p).range_fiberι (IsLocalRing.closedPoint R)).symm.subset hbaseb
  have hspγ : specializationCycle (j ≫ p) r
      ((fun s ↦ fiberCycleRestrict p (j ≫ p) j rfl s r (β s))
        (genericPoint (Spec (.of R)))) =
      (fun s ↦ fiberCycleRestrict p (j ≫ p) j rfl s r (β s)) (IsLocalRing.closedPoint R) := by
    have h1 := specializationCycle_fiberCycleRestrict p (j ≫ p) j rfl r
      (β (genericPoint (Spec (.of R))))
    rwa [hsp] at h1
  have hV := mem_supportOfFamily_iff_of_isIntegral_over_dvr (j ≫ p) r
    (fun s ↦ fiberCycleRestrict p (j ≫ p) j rfl s r (β s)) hspγ hbasea hbaseb
  rw [mem_supportOfFamily_fiberCycleRestrict_iff p (j ≫ p) j rfl r β _ ya a' hya,
    mem_supportOfFamily_fiberCycleRestrict_iff p (j ≫ p) j rfl r β _ yb b' hyb,
    ha', hb'] at hV
  exact hV

/-- Over the spectrum of a discrete valuation ring, membership in the support of a family of
`r`-cycles satisfying the valuative condition is unchanged along a specialization from the
generic fibre to the special fibre of a morphism smooth of relative dimension `r`.

The total space is regular, being smooth over a regular ring, hence normal; so the connected
component of the point of the special fibre is an open and closed integral subscheme, and the
point of the generic fibre lies in it because that component is open. The statement for an
integral total space applies to it. -/
private theorem mem_supportOfFamily_iff_of_specializes_over_dvr {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (r : ℕ) [SmoothOfRelativeDimension r p] (β : FamilyOfCycles p r)
    (hsp : specializationCycle p r (β (genericPoint (Spec (.of R)))) =
      β (IsLocalRing.closedPoint R))
    {a b : Y} (ha : p a = genericPoint (Spec (.of R)))
    (hb : p b = IsLocalRing.closedPoint R) (hab : a ⤳ b) :
    (a ∈ supportOfFamily p β ↔ b ∈ supportOfFamily p β) := by
  let : Smooth p := SmoothOfRelativeDimension.smooth r p
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hopen : IsOpen (connectedComponent b) :=
    isOpen_connectedComponent_of_isLocallyNoetherian b
  set V : Y.Opens := ⟨connectedComponent b, hopen⟩ with hVdef
  let : ConnectedSpace (V : Scheme.{u}) := by
    rw [hVdef]
    exact Subtype.connectedSpace (s := connectedComponent b) isConnected_connectedComponent
  let : SmoothOfRelativeDimension r (V.ι ≫ p) :=
    smoothOfRelativeDimension_comp_of_isOpenImmersion V.ι p r
  let : Smooth (V.ι ≫ p) := SmoothOfRelativeDimension.smooth r _
  let : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  let : IsLocallyNoetherian (V : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
  let : IsNormal (V : Scheme.{u}) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_regular (V.ι ≫ p))
  let : AlgebraicGeometry.IsIntegral (V : Scheme.{u}) :=
    isIntegral_of_connectedSpace_of_isNormal
  have hbV : b ∈ Set.range (V.ι : (V : Scheme.{u}) ⟶ Y).base := by
    rw [Scheme.Opens.range_ι, hVdef]
    exact mem_connectedComponent
  have haV : a ∈ Set.range (V.ι : (V : Scheme.{u}) ⟶ Y).base := by
    rw [Scheme.Opens.range_ι, hVdef]
    exact hab.mem_open hopen mem_connectedComponent
  obtain ⟨b', hb'⟩ := hbV
  obtain ⟨a', ha'⟩ := haV
  exact mem_supportOfFamily_iff_of_isIntegral_piece_over_dvr p r β hsp V.ι ha' hb' ha hb

/-! ### The support of a smooth relative cycle -/

/-- **Stacks Project, Lemma 0H5B.** Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be
smooth of relative dimension `r` and let `α` be a relative `r`-cycle on `X/S`. Then the support
of `α` is open and closed in `X`.

By the reduction step it suffices to know that membership in the support is unchanged along
every specialization `x ⤳ y` of points of `X`. Such a specialization is realized by the
generic-to-closed specialization on the spectrum of a discrete valuation ring `R` mapping to
`X`, and the base change `X ×_S Spec R ⟶ Spec R` — again smooth of relative dimension `r` —
carries a section through which the two points are seen. The valuative condition applies there,
and compatibility of supports with base change transports the conclusion back to `X`. -/
@[stacks 0H5B]
theorem isClopen_supportOfFamily_of_smoothOfRelativeDimension {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) [SmoothOfRelativeDimension r f]
    (α : FamilyOfCycles f r) (hα : IsRelativeCycle f r α) :
    IsClopen (supportOfFamily f α) := by
  refine isClopen_supportOfFamily_of_specializes f α fun x y hxy ↦ ?_
  let : Smooth f := SmoothOfRelativeDimension.smooth r f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨R, _, _, _, h, hη, hs⟩ := AlgebraicGeometry.exists_dvr_morphism_of_specializes X hxy
  obtain ⟨g, hgf⟩ : ∃ g : (Spec (.of R) : Scheme.{u}) ⟶ S, h ≫ f = g := ⟨h ≫ f, rfl⟩
  have hcomm : h ≫ f =
      (𝟙 (Spec (.of R) : Scheme.{u}) : (Spec (.of R) : Scheme.{u}) ⟶ _) ≫ g := by
    rw [hgf, Category.id_comp]
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : (Spec (.of R) : Scheme.{u}) ⟶ (pullback f g : Scheme.{u}),
      (∀ t, pullback.fst f g (l t) = h t) ∧ ∀ t, pullback.snd f g (l t) = t := by
    refine ⟨pullback.lift h (𝟙 _) hcomm, fun t ↦ ?_, fun t ↦ ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
      rfl
  let : SmoothOfRelativeDimension r (pullback.snd f g) :=
    smoothOfRelativeDimension_pullback_snd f g r
  have hkey := mem_supportOfFamily_iff_of_specializes_over_dvr (pullback.snd f g) r
    (baseChangeFamily f g r α) (hα R g) (a := l (genericPoint (Spec (.of R))))
    (b := l (IsLocalRing.closedPoint R)) (hl₂ _) (hl₂ _)
    ((IsLocalRing.specializes_closedPoint _).map l.continuous)
  rw [supportOfFamily_baseChangeFamily f g r α, Set.mem_preimage, Set.mem_preimage,
    hl₁ (genericPoint (Spec (.of R))), hl₁ (IsLocalRing.closedPoint R), hη, hs] at hkey
  exact hkey

end Stacks.Chow

end
