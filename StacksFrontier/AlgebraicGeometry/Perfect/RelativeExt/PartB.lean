module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartBExt
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictPhi
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartA
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentHocolim
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits

/-!
# [Stacks, Tag 08IF] (B): relative `Ext` is represented by a pseudo-coherent complex

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` an object of
`D^-_{Coh}(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S`. There is a pseudo-coherent `L` in `D(𝒪_S)` and isomorphisms

`Ext^i_{𝒪_S}(L, ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`

for quasi-coherent `ℱ`, functorial in `ℱ` and compatible with the boundary maps.

The proof is the source's. As in (A), replace `X` by a Noetherian open `U` containing the support
of `𝒢`. There `E|_U` is pseudo-coherent ([Stacks, Tag 08E8]), hence `E|_U = hocolim Eₙ` with
`Eₙ` perfect and `τ_{≥ -n} Eₙ ≅ τ_{≥ -n} E|_U` ([Stacks, Tag 0DJN]). With
`Kₙ = R(f|_U)_*(Eₙ^∨ ⊗^L 𝒢|_U)` perfect ([Stacks, Tag 0DJQ]) and `Lₙ = Kₙ^∨`, the system
`L₀ ⟶ L₁ ⟶ ⋯` of `Stacks.Cohomology.RelativeExt.partBSystem` has a homotopy colimit `L`, whose
cohomology is the colimit of that of the `Lₙ` ([Stacks, Tag 0CRK]); `L` is pseudo-coherent
([Stacks, Tag 0DJN]) and `Stacks.Cohomology.RelativeExt.exists_relativeExtIso_of_open` gives the
isomorphisms.

## Main definitions

* `Stacks.Cohomology.RelativeExt.pseudoCoherentRepresentative`: a choice of `L`.

## Main results

* `Stacks.Cohomology.RelativeExt.partBHomologyColimit_of_isHomotopyColimitWith`: the cohomology of
  `L` is the colimit of that of the `Lₙ` ([Stacks, Tag 0CRK]).
* `Stacks.Cohomology.RelativeExt.exists_pseudoCoherent_relativeExt_representative`:
  [Stacks, Tag 08IF] (B).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

/-- **The cohomology sheaves of `L = hocolim Lₙ` are the colimits of those of the `Lₙ`**
([Stacks, Tag 0CRK]): cohomology sheaves are homological and commute with countable direct
sums, and colimits over `ℕ` of `𝒪_S`-modules are exact. -/
theorem partBHomologyColimit_of_isHomotopyColimitWith {U S : Scheme.{u}} {g : U ⟶ S}
    {G : CochainComplex (TModules U.toRingedSpace) ℤ} {E : DStd U} (D : PartBApproxSystem g G E)
    [HasCoproduct (partBSystem D).obj] {L : DStd S} {d : ∀ n, (partBSystem D).obj n ⟶ L}
    (hL : IsHomotopyColimitWith (partBSystem D) L d)
    [∀ i : ℤ, HasColimit (partBSystem D ⋙ @DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) _ _ (HasDerivedCategory.standard _) i)] :
    PartBHomologyColimit D L d := by
  intro i
  obtain ⟨p, q, hT, hc⟩ := hL
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :=
    Stacks.PseudoCoherentHocolim.hasExactColimitsOfShape_nat_modules S
  have : PreservesColimitsOfShape (Discrete ℕ) (@DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) _ _
      (HasDerivedCategory.standard _) i) :=
    @Stacks.PseudoCoherentHocolim.preservesColimitsOfShape_discrete_nat_homologyFunctor S
      (HasDerivedCategory.standard _) i
  obtain ⟨e, he⟩ := CategoryTheory.Pretriangulated.exists_iso_colimit_of_isHomotopyColimit
    (partBSystem D) (@DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing S.toRingedSpace)) _ _ (HasDerivedCategory.standard _) i) p q hT
  exact ⟨e, fun n => (he n).trans (congrArg _ (hc n))⟩

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]

/-- **The data of the construction of [Stacks, Tag 08IF] (B).** A quasi-compact (hence
Noetherian) open `V ⊇ Supp 𝒢` of `X` on which restriction of the relative `Ext` groups is
bijective; the approximating system `D` of `E|_V` by perfect objects (`PartBApproxSystem`) with
`𝒢` living in degrees `≥ b`; a homotopy colimit `L = hocolim Lₙ` of the system `Lₙ = Kₙ^∨` of
`partBSystem D`, with coprojections `d`, whose cohomology is the colimit of that of the `Lₙ`; the
glued unit `η : E|_V ⟶ Φ(L)`; and pseudo-coherence of `L`. -/
structure PartBWitness (E : DStd X) (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) where
  /-- The open `V ⊇ Supp 𝒢`. -/
  V : X.Opens
  isCompact : IsCompact (V : Set X)
  isNoetherian : IsNoetherian (V : Scheme.{u})
  quasiCompact : QuasiCompact (V.ι ≫ f)
  quasiSeparated : QuasiSeparated (V.ι ≫ f)
  /-- The stalks of `𝒢` vanish off `V`. -/
  support : ∀ (q : ℤ) (x : X), x ∉ (V : Set X) →
    IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x)
  /-- A closed `Z` with `Supp 𝒢 ⊆ Z ⊆ V`. -/
  Z : Set X
  isClosed : IsClosed Z
  hZV : Z ⊆ (V : Set X)
  /-- The stalks of `𝒢` vanish off `Z`. -/
  supportZ : ∀ (q : ℤ) (x : X), x ∉ Z →
    IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x)
  /-- Restriction to `V` is bijective on the relative `Ext` groups. -/
  res : ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ),
    Function.Bijective (restrictRelativeExt f V.ι G E F i)
  /-- `𝒢` lives in degrees `≥ b`. -/
  b : ℤ
  hb : G.IsStrictlyGE b
  /-- The approximating system of `E|_V`. -/
  D : PartBApproxSystem (V.ι ≫ f) (restrictComplex V.ι G) ((restrictDerived V.ι).obj E)
  hasCoproduct : HasCoproduct (partBSystem D).obj
  /-- `L = hocolim Lₙ`. -/
  L : DStd S
  /-- The coprojections `dₙ : Lₙ ⟶ L`. -/
  d : ∀ n, (partBSystem D).obj n ⟶ L
  hocolim : letI := hasCoproduct; IsHomotopyColimitWith (partBSystem D) L d
  hasColimit : ∀ i : ℤ, HasColimit (partBSystem D ⋙ @DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) _ _ (HasDerivedCategory.standard _) i)
  homologyColimit : letI := hasColimit; PartBHomologyColimit D L d
  /-- The glued unit `η : E|_V ⟶ Φ(L)`. -/
  η : (restrictDerived V.ι).obj E ⟶ (partBΦ (isBoundedFlatOver_restrictComplex (f := f) (j := V.ι)
    (isBoundedFlatOver_of_flatProperSupportComplex hG))).obj L
  hη : ∀ n, D.c n ≫ η = partBUnit D (isBoundedFlatOver_restrictComplex (f := f) (j := V.ι)
      (isBoundedFlatOver_of_flatProperSupportComplex hG)) n ≫
    (partBΦ (isBoundedFlatOver_restrictComplex (f := f) (j := V.ι)
      (isBoundedFlatOver_of_flatProperSupportComplex hG))).map (d n)
  /-- `L` is pseudo-coherent. -/
  isPseudoCoherent : IsPseudoCoherentObject L

/-- **The construction of [Stacks, Tag 08IF] (B) can be carried out.** -/
theorem nonempty_partBWitness (E : DStd X) (hE : IsBoundedAboveCoherent E)
    (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) :
    Nonempty (PartBWitness f E G hG) := by
  have hG' := isBoundedFlatOver_of_flatProperSupportComplex hG
  obtain ⟨b, -, hb, -⟩ := hG.bounded
  obtain ⟨Z, hZp, hZs⟩ := hG.properSupport
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hZc : IsCompact (Z : Set X) := isCompact_of_isProperOver f Z hZp
  obtain ⟨V, hZV, hVc⟩ := exists_isCompact_open_superset X Z hZc
  have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  have hVN : IsNoetherian (V : Scheme.{u}) := {}
  have hqc : QuasiCompact (V.ι ≫ f) := inferInstance
  have hqs : QuasiSeparated (V.ι ≫ f) := inferInstance
  have hGU := flatProperSupportComplex_restrictComplex f V G hG Z hZp hZs hZV
  -- the restriction to `V` is bijective on the relative `Ext` groups
  have hGZ : ∀ (q : ℤ) (x : X), x ∉ (Z : Set X) →
      IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x) := fun q x hx =>
    isZero_stalk_of_supp_subset (G.X q) Z (hZs q) x hx
  have hres : ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ),
      Function.Bijective (restrictRelativeExt f V.ι G E F i) := fun F i =>
    restrictRelativeExt_bijective_of f V.ι E F i
      (bijective_derivedPullback_map_of_supportedOn V.ι Z Z.isClosed
        (hZV.trans_eq V.range_ι.symm) E _
        (cohomologySupportedOn_relativeExtTarget_shift (f := f) (G := G) (Z : Set X) hGZ F i))
  -- `E|_V = hocolim Eₙ` with `Eₙ` perfect ([Stacks, Tag 0DJN])
  have hpc := (isPseudoCoherent_restrictDerived V E hE).1
  obtain ⟨FE, hcop, c, hperf, -, hhoc, htr⟩ :=
    @Stacks.PseudoCoherentHocolim.exists_perfect_hocolim_of_isPseudoCoherent_of_supportedOn
      (V : Scheme.{u}) (HasDerivedCategory.standard _) _ _ Set.univ isClosed_univ (by simp)
      ((restrictDerived V.ι).obj E) (fun _ _ hx => absurd trivial hx) hpc
  have hK : ∀ n, IsPerfectObject (stageK (V.ι ≫ f).toLRSHom.toShHom
      (X := (V : Scheme.{u}).toRingedSpace) (G := restrictComplex V.ι G) (FE.obj n)) := fun n =>
    Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect
      (V.ι ≫ f) _ _ _ (isPerfectObject_derivedDual (FE.obj n) (hperf n)) hGU
  have hLq : ∀ n, qcohDerived S (stageL (V.ι ≫ f).toLRSHom.toShHom
      (X := (V : Scheme.{u}).toRingedSpace) (G := restrictComplex V.ι G) (FE.obj n)) :=
    fun n i => @Stacks.PseudoCoherentHocolim.isQuasicoherent_homology_of_isPseudoCoherent S
      (HasDerivedCategory.standard _) _
      (@Stacks.PseudoCoherentHocolim.isPseudoCoherent_of_isPerfect S
        (HasDerivedCategory.standard _) _ (isPerfectObject_derivedDual _ (hK n))) i
  let D : PartBApproxSystem (V.ι ≫ f) (restrictComplex V.ι G) ((restrictDerived V.ι).obj E) :=
    { sys := FE
      hasCoproduct := hcop
      c := c
      perfect := fun n => isPerfect_ringedSite_of_isPerfectObject _ (hperf n)
      hocolim := hhoc
      trunc := htr
      projFormula := fun n N hN =>
        Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh
          (V.ι ≫ f) _ N (isDQCoh_stageSource (V.ι ≫ f) (FE.obj n) (hperf n) _ hGU) hN
      stageKPerfect := fun n => isPerfect_ringedSite_of_isPerfectObject _ (hK n)
      stageLQCoh := hLq }
  -- `L = hocolim Lₙ`
  have hcopS : HasColimitsOfShape (Discrete ℕ) (DStd S) :=
    @Stacks.PseudoCoherentHocolim.hasColimitsOfShape_discrete_nat_derivedCategory S
      (HasDerivedCategory.standard _)
  obtain ⟨L, d, hL⟩ := exists_isHomotopyColimitWith_partBSystem D
  have hcolim := partBHomologyColimit_of_isHomotopyColimitWith D hL
  have hGVU := isBoundedFlatOver_restrictComplex (f := f) (j := V.ι) hG'
  obtain ⟨η, hη⟩ := exists_partBHocolimUnit D hGVU hL
  -- `L` is pseudo-coherent ([Stacks, Tag 0DJN])
  have hLpc : IsPseudoCoherentObject L := by
    refine @Stacks.PseudoCoherentHocolim.isPseudoCoherent_of_forall_exists_perfect_isIso
      S.toRingedSpace (HasDerivedCategory.standard _) L fun k => ?_
    obtain ⟨n, hn⟩ := exists_isIso_homology_partBCoprojection D hGVU b
      (isStrictlyGE_restrictComplex (j := V.ι) b hb) hcolim k
    exact ⟨partBL D n, d n, isPerfectObject_derivedDual _ (hK n), hn⟩
  exact ⟨⟨V, hVc, hVN, hqc, hqs, fun q x hx => hGZ q x fun hxZ => hx (hZV hxZ), (Z : Set X),
    Z.isClosed, hZV, hGZ, hres, b, hb, D,
    inferInstance, L, d, hL, fun _ => inferInstance, hcolim, η, hη, hLpc⟩⟩

section Representative

variable (E : DStd X) (hE : IsBoundedAboveCoherent E)
  (G : CochainComplex (TModules X.toRingedSpace) ℤ)
  (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G)

/-- **The chosen data of the construction of [Stacks, Tag 08IF] (B).** -/
def partBWitness : PartBWitness f E G hG :=
  Classical.choice (nonempty_partBWitness f E hE G hG)

/-- **The pseudo-coherent complex `L` of [Stacks, Tag 08IF] (B)**: the homotopy colimit `L` of the
chosen data `partBWitness`. -/
def pseudoCoherentRepresentative : DStd S := (partBWitness f E hE G hG).L

/-- The complex `pseudoCoherentRepresentative f E hE G hG` is pseudo-coherent. -/
theorem isPseudoCoherent_pseudoCoherentRepresentative :
    IsPseudoCoherentObject (pseudoCoherentRepresentative f E hE G hG) :=
  (partBWitness f E hE G hG).isPseudoCoherent

/-- **`Ext^i_{𝒪_S}(L, ℱ) ≃+ Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ)`** for quasi-coherent `ℱ`: the isomorphism
`relativeExtIsoOfOpen` of the chosen data, i.e. `partBExtIso` on the open `V` followed by the
inverse of restriction to `V`. -/
def pseudoCoherentRepresentativeExtEquiv (i : ℤ)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    baseExtGroup (pseudoCoherentRepresentative f E hE G hG) F i ≃+ relativeExtGroup f G E F i :=
  letI := (partBWitness f E hE G hG).hasCoproduct
  letI := (partBWitness f E hE G hG).hasColimit
  relativeExtIsoOfOpen f (partBWitness f E hE G hG).V.ι
    (isBoundedFlatOver_of_flatProperSupportComplex hG) E (partBWitness f E hE G hG).D
    (partBWitness f E hE G hG).b (partBWitness f E hE G hG).hb
    (partBWitness f E hE G hG).hocolim (partBWitness f E hE G hG).homologyColimit
    (partBWitness f E hE G hG).res (partBWitness f E hE G hG).η
    (partBWitness f E hE G hG).hη i F hF

/-- The isomorphisms `pseudoCoherentRepresentativeExtEquiv` are natural in the quasi-coherent
module `ℱ`: they commute with the maps induced by a morphism `v : ℱ ⟶ ℱ'`. -/
theorem pseudoCoherentRepresentativeExtEquiv_naturality (i : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hF : F.IsQuasicoherent)
    (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
    (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) F i) :
    pseudoCoherentRepresentativeExtEquiv f E hE G hG i F' hF'
        (baseExtMap (pseudoCoherentRepresentative f E hE G hG) i v z) =
      relativeExtMap f G E i v (pseudoCoherentRepresentativeExtEquiv f E hE G hG i F hF z) :=
  let := (partBWitness f E hE G hG).hasCoproduct
  let := (partBWitness f E hE G hG).hasColimit
  relativeExtIsoOfOpen_naturality _ _ _ _ _ _ _ _ _ _ _ _ i hF hF' v z

/-- The isomorphisms `pseudoCoherentRepresentativeExtEquiv` commute with the boundary maps
attached to a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of modules with `ℱ₁` and `ℱ₃`
quasi-coherent. -/
theorem pseudoCoherentRepresentativeExtEquiv_boundary
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent) (n m : ℤ)
    (h : 1 + n = m) (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) A.X₃ n) :
    pseudoCoherentRepresentativeExtEquiv f E hE G hG m A.X₁ h₁
        (baseExtBoundaryMap (pseudoCoherentRepresentative f E hE G hG) hA n m h z) =
      relativeExtBoundaryMap E (isBoundedFlatOver_of_flatProperSupportComplex hG) hA n m h
        (pseudoCoherentRepresentativeExtEquiv f E hE G hG n A.X₃ h₃ z) :=
  let := (partBWitness f E hE G hG).hasCoproduct
  let := (partBWitness f E hE G hG).hasColimit
  relativeExtIsoOfOpen_boundary _ _ _ _ _ _ _ _ _ _ _ _ hA h₁ h₃ n m h z

/-- The restriction `D(j^*) : Hom(E, Φ N) ⟶ Hom(E|_V, D(j^*)(Φ N))` is bijective for the chosen
`V`, `Φ N` being supported on `Z ⊆ V`. -/
theorem bijective_restrictDerived_map_pseudoCoherentRepresentative (N : DStd S) :
    Function.Bijective (fun φ : E ⟶ (pullbackTensorDerivedFunctor
        (isBoundedFlatOver_of_flatProperSupportComplex hG)).obj N =>
      (restrictDerived (partBWitness f E hE G hG).V.ι).map φ) :=
  bijective_restrictDerived_map_of (partBWitness f E hE G hG).V.ι E _
    (bijective_derivedPullback_map_of_supportedOn (partBWitness f E hE G hG).V.ι
      (partBWitness f E hE G hG).Z (partBWitness f E hE G hG).isClosed
      ((partBWitness f E hE G hG).hZV.trans_eq (Scheme.Opens.range_ι _).symm) E _
      (cohomologySupportedOn_pullbackTensorDerivedFunctor_obj f.toLRSHom.toShHom G
        (isBoundedFlatOver_of_flatProperSupportComplex hG) (partBWitness f E hE G hG).Z
        (partBWitness f E hE G hG).supportZ N))

/-- **`Hom(L, N) ≃ Hom(E, Φ N)`, naturally in `N ∈ D^+_QCoh(𝒪_S)`**, `Φ = Lf^*(-) ⊗^L 𝒢`: on the
chosen open `V`, composition with the glued unit `η : E|_V ⟶ Φ_V(L)`; then `Φ_V ≅ Φ ⋙ D(j^*)`
(`pullbackTensorDerivedRestrictIso`); then the inverse of restriction to `V`, bijective because
`Φ N` is supported on `Z ⊆ V`. -/
def pseudoCoherentRepresentativeHomEquiv :
    ShiftedHom.NaturalHomEquiv (𝟭 (DStd S))
      (pullbackTensorDerivedFunctor (isBoundedFlatOver_of_flatProperSupportComplex hG))
      (pseudoCoherentRepresentative f E hE G hG) E (plusQCohDerived S) where
  equiv N hN :=
    letI := (partBWitness f E hE G hG).hasCoproduct
    letI := (partBWitness f E hE G hG).hasColimit
    (Equiv.ofBijective _ (bijective_partBHocolimUnit_comp (partBWitness f E hE G hG).D
      (isBoundedFlatOver_restrictComplex (f := f) (j := (partBWitness f E hE G hG).V.ι)
        (isBoundedFlatOver_of_flatProperSupportComplex hG))
      (partBWitness f E hE G hG).hocolim (partBWitness f E hE G hG).b
      (isStrictlyGE_restrictComplex (j := (partBWitness f E hE G hG).V.ι)
        (partBWitness f E hE G hG).b (partBWitness f E hE G hG).hb)
      (partBWitness f E hE G hG).homologyColimit (partBWitness f E hE G hG).η
      (partBWitness f E hE G hG).hη N hN.1 hN.2.choose hN.2.choose_spec)).trans
    ((((pullbackTensorDerivedRestrictIso f (partBWitness f E hE G hG).V.ι
        (isBoundedFlatOver_of_flatProperSupportComplex hG)).app N).homToEquiv).trans
      (Equiv.ofBijective _
        (bijective_restrictDerived_map_pseudoCoherentRepresentative f E hE G hG N)).symm)
  naturality {N N'} hN hN' k ψ := by
    letI := (partBWitness f E hE G hG).hasCoproduct
    letI := (partBWitness f E hE G hG).hasColimit
    apply (bijective_restrictDerived_map_pseudoCoherentRepresentative f E hE G hG N').1
    have e := fun (N₀ : DStd S) (y : (restrictDerived (partBWitness f E hE G hG).V.ι).obj E ⟶
        (restrictDerived (partBWitness f E hE G hG).V.ι).obj
          ((pullbackTensorDerivedFunctor (isBoundedFlatOver_of_flatProperSupportComplex hG)).obj
            N₀)) =>
      (Equiv.ofBijective _ (bijective_restrictDerived_map_pseudoCoherentRepresentative
        f E hE G hG N₀)).apply_symm_apply y
    have hR := (pullbackTensorDerivedRestrictIso f (partBWitness f E hE G hG).V.ι
      (isBoundedFlatOver_of_flatProperSupportComplex hG)).hom.naturality k
    refine (e N' _).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (restrictDerived (partBWitness f E hE G hG).V.ι).map
      ((pullbackTensorDerivedFunctor (isBoundedFlatOver_of_flatProperSupportComplex hG)).map k))
      (e N _)).symm |>.trans
        ((restrictDerived (partBWitness f E hE G hG).V.ι).map_comp _ _).symm
    exact (congrArg (· ≫ _) ((congrArg (_ ≫ ·) ((partBΦ _).map_comp _ _)).trans
      (Category.assoc _ _ _).symm)).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hR).trans (Category.assoc _ _ _).symm))

/-- **`pseudoCoherentRepresentativeHomEquiv` restricted to `V`** is composition with `η`
followed by `Φ_V ≅ Φ ⋙ D(j^*)`. -/
theorem restrictDerived_map_pseudoCoherentRepresentativeHomEquiv (N : DStd S)
    (hN : plusQCohDerived S N) (ψ : pseudoCoherentRepresentative f E hE G hG ⟶ N) :
    (restrictDerived (partBWitness f E hE G hG).V.ι).map
        ((pseudoCoherentRepresentativeHomEquiv f E hE G hG).equiv N hN ψ) =
      ((partBWitness f E hE G hG).η ≫
        (partBΦ (isBoundedFlatOver_restrictComplex (f := f) (j := (partBWitness f E hE G hG).V.ι)
          (isBoundedFlatOver_of_flatProperSupportComplex hG))).map ψ) ≫
        (pullbackTensorDerivedRestrictIso f (partBWitness f E hE G hG).V.ι
          (isBoundedFlatOver_of_flatProperSupportComplex hG)).hom.app N :=
  (Equiv.ofBijective _ (bijective_restrictDerived_map_pseudoCoherentRepresentative
    f E hE G hG N)).apply_symm_apply _

/-- **`pseudoCoherentRepresentativeExtEquiv` restricted to `V` is `partBExtIso`** of the chosen
data. -/
theorem restrictRelativeExt_pseudoCoherentRepresentativeExtEquiv (i : ℤ)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent)
    (z : baseExtGroup (pseudoCoherentRepresentative f E hE G hG) F i) :
    letI := (partBWitness f E hE G hG).hasCoproduct
    letI := (partBWitness f E hE G hG).hasColimit
    restrictRelativeExt f (partBWitness f E hE G hG).V.ι G E F i
        (pseudoCoherentRepresentativeExtEquiv f E hE G hG i F hF z) =
      partBExtIso (partBWitness f E hE G hG).D
        (isBoundedFlatOver_restrictComplex (f := f) (j := (partBWitness f E hE G hG).V.ι)
          (isBoundedFlatOver_of_flatProperSupportComplex hG))
        (partBWitness f E hE G hG).hocolim (partBWitness f E hE G hG).b
        (isStrictlyGE_restrictComplex (j := (partBWitness f E hE G hG).V.ι)
          (partBWitness f E hE G hG).b (partBWitness f E hE G hG).hb)
        (partBWitness f E hE G hG).homologyColimit (partBWitness f E hE G hG).η
        (partBWitness f E hE G hG).hη i F hF z :=
  let := (partBWitness f E hE G hG).hasCoproduct
  let := (partBWitness f E hE G hG).hasColimit
  restrictRelativeExt_relativeExtIsoOfOpen _ _ _ _ _ _ _ _ _ _ _ _ i F hF z

end Representative

/-- **[Stacks, Tag 08IF] (B).** Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of
finite type, `E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over
`S`, with support proper over `S`. There is a pseudo-coherent object `L` of `D(𝒪_S)` and
isomorphisms

`Ext^i_{𝒪_S}(L, ℱ) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`

for all `i` and all quasi-coherent `ℱ`, functorial in `ℱ` and compatible with the boundary maps of
short exact sequences `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of quasi-coherent modules (on the left, composition
with the connecting morphism `ℱ₃ ⟶ ℱ₁[1]`; on the right, with that of
`0 ⟶ 𝒢 ⊗ f^*ℱ₁ ⟶ 𝒢 ⊗ f^*ℱ₂ ⟶ 𝒢 ⊗ f^*ℱ₃ ⟶ 0`, exact because `𝒢` is flat over `S`). -/
@[stacks 08IF "(B)"]
theorem exists_pseudoCoherent_relativeExt_representative (E : DStd X)
    (hE : IsBoundedAboveCoherent E) (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) :
    ∃ L : DStd S, IsPseudoCoherentObject L ∧
      ∃ β : ∀ (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)),
          F.IsQuasicoherent → (baseExtGroup L F i ≃+ relativeExtGroup f G E F i),
        (∀ (i : ℤ) (F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
            (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
            (z : baseExtGroup L F i),
          β i F' hF' (baseExtMap L i v z) = relativeExtMap f G E i v (β i F hF z)) ∧
        (∀ (A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
            (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent)
            (n m : ℤ) (h : 1 + n = m) (z : baseExtGroup L A.X₃ n),
          β m A.X₁ h₁ (baseExtBoundaryMap L hA n m h z) =
            relativeExtBoundaryMap E (isBoundedFlatOver_of_flatProperSupportComplex hG) hA n m
              h (β n A.X₃ h₃ z)) :=
  ⟨pseudoCoherentRepresentative f E hE G hG,
    isPseudoCoherent_pseudoCoherentRepresentative f E hE G hG,
    pseudoCoherentRepresentativeExtEquiv f E hE G hG,
    fun i _ _ hF hF' v z =>
      pseudoCoherentRepresentativeExtEquiv_naturality f E hE G hG i hF hF' v z,
    fun _ hA h₁ h₃ n m h z =>
      pseudoCoherentRepresentativeExtEquiv_boundary f E hE G hG hA h₁ h₃ n m h z⟩

end Stacks.Cohomology.RelativeExt

end
