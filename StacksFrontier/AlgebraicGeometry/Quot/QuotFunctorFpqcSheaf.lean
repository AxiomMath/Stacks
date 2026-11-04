module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFinitePresentationOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.TestSchemePullbacks

/-!
# The functors of quotients and the Quot functor are fpqc sheaves (Stacks 082P, 09TT)

In Situation 082M — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — the functor of quotients
`Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets` and its finite-presentation subfunctor `Q^{fp}_{F/X/Y}` satisfy
the sheaf property for the fpqc topology (Stacks 082P); and in Situation 09TR, where `f` is
moreover of finite presentation, so does the Quot functor `Quot_{F/X/Y}` (Stacks 09TT).

The fpqc topology is `AlgebraicGeometry.Space.fpqcTopology`, the topology on the test schemes over
`Y` whose covering sieves are those containing an fpqc covering family of schemes (Stacks 03X6:
the sheaf property for every fpqc covering).  A covering presieve of it is an fpqc covering
`{g i : U i ⟶ T}` of test schemes, and the sheaf condition for it is
`AlgebraicGeometry.Space.QuotientSituation.isSheafFor_quotientSubfunctor`: a compatible family of
quotients descends to a unique quotient of `F_T` with quasi-coherent quotient module, which is
Remark 08IU for the fpqc covering `{X_{U i} ⟶ X_T}` of Stacks 03MR.  What is added here is the
descent of the conditions cutting out each functor, exactly as in the proofs of the source:

* flatness over the test scheme descends by Stacks 05VY
  (`AlgebraicGeometry.Space.isFlatOver_of_isFpqcCovering_of_isFlatOver_modulePullback`), after
  composing flatness over `U i` with the flat morphism `U i ⟶ T` (Stacks 05VX);
* finite presentation descends by Stacks 060V
  (`AlgebraicGeometry.Space.isFinitePresentationOnSite_of_pullback_fpqc`);
* proper support descends by Stacks 0422, read through Stacks 07TZ and Stacks 0CZC
  (`AlgebraicGeometry.Space.hasProperSupport_of_isFpqcCovering`).

The source also reads the Quot functor as a presheaf on the big fppf site of `S`, sending a scheme
`T` to the pairs `(h : T ⟶ Y, Q)`; that presheaf is
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`.  It satisfies the sheaf property for
the fpqc topology of the big fppf site of `S`, the morphisms `h` glueing because the algebraic
space `Y` is an fpqc sheaf (Stacks 0APL), and hence for the fppf topology, which is the form
Stacks 09TU consumes.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.quotientsFunctor_isSheaf_fpqcTopology` and
  `QuotientSituation.finitePresentationQuotientsFunctor_isSheaf_fpqcTopology`: **Stacks 082P**.
* `AlgebraicGeometry.Space.QuotSituation.quotFunctor_isSheaf_fpqcTopology`: **Stacks 09TT**.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fpqc`: Stacks 09TT for the
  presheaf of pairs on the big fppf site of `S`.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fppf`: the fppf sheaf property
  of that presheaf, for Stacks 09TU.
* `AlgebraicGeometry.Space.QuotSituation.quotientsSeparatedForCoverings_properlySupportedQuotients`
  and `…quotientsGlueAlongCoverings_properlySupportedQuotients`, and their analogues for
  `Q_{F/X/Y}` and `Q^{fp}_{F/X/Y}`: the hypotheses carried by the fppf statements of Stacks 082P
  and Stacks 09TT in `StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSheaf.lean` and
  `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorSheaf.lean` are theorems.

## References

* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 03X6](https://stacks.math.columbia.edu/tag/03X6)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 060V](https://stacks.math.columbia.edu/tag/060V)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance] pointTopology

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Descent of the conditions -/

section Conditions

variable {I : Type v} {T : SchemesOver D.Y} {U : I → SchemesOver D.Y} (g : ∀ i, U i ⟶ T)
  (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
include hg

/-- **Flatness over the test scheme descends along an fpqc covering** of it, by Stacks 05VY:
the pullbacks of the quotient module are flat over the `U i`, hence over `T` along the flat
morphisms `U i ⟶ T` (Stacks 05VX), and `{X_{U i} ⟶ X_T}` is an fpqc covering. -/
theorem mem_quotients_of_isFpqcCovering (K₀ : Subobject (D.baseChangeModule T))
    (hqc : (D.quotientModule T K₀).IsQuasicoherentOnSite)
    (h : ∀ i, D.quotientPullback (g i) K₀ ∈ D.quotients (U i)) : K₀ ∈ D.quotients T := by
  refine ⟨hqc, ?_⟩
  have := hqc
  refine isFlatOver_of_isFpqcCovering_of_isFlatOver_modulePullback B S hS
    (fun i ↦ D.relativeMap (g i)) (isFpqcCovering_baseChangeMap D.f g hg) (D.projection T) _
    fun i ↦ ?_
  have hpb : ((modulePullback B S hS (D.relativeMap (g i))).obj
      (D.quotientModule T K₀)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hqc
  have hflat : IsFlatOver B S hS (D.space (U i)).2 (D.projection (U i)).hom
      ((modulePullback B S hS (D.relativeMap (g i))).obj (D.quotientModule T K₀)) :=
    IsFlatOver.of_iso B S hS _ (D.quotientPullbackCokernelIso (g i) K₀) (h i).2
  have e : D.relativeMap (g i) ≫ D.projection T =
      D.projection (U i) ≫ (schemeSpaceFunctor B S hS).map (g i).left :=
    baseChangeMap_comp_inclusion D.f (g i)
  rw [e]
  exact isFlatOver_comp_of_isFlat B S hS (D.projection (U i))
    ((schemeSpaceFunctor B S hS).map (g i).left) _ hflat (hg.1 i)

/-- **Finite presentation of the quotient descends along an fpqc covering** of the test
scheme, by Stacks 060V. -/
theorem mem_finitePresentationQuotients_of_isFpqcCovering (K₀ : Subobject (D.baseChangeModule T))
    (hqc : (D.quotientModule T K₀).IsQuasicoherentOnSite)
    (h : ∀ i, D.quotientPullback (g i) K₀ ∈ D.finitePresentationQuotients (U i)) :
    K₀ ∈ D.finitePresentationQuotients T :=
  ⟨D.mem_quotients_of_isFpqcCovering g hg K₀ hqc fun i ↦ (h i).1,
    isFinitePresentationOnSite_of_pullback_fpqc B S hS _ (fun i ↦ D.relativeMap (g i)) _ hqc
      (isFpqcCovering_baseChangeMap D.f g hg) fun i ↦
        SheafOfModules.IsFinitePresentationOnSite.of_iso
          (D.quotientPullbackCokernelIso (g i) K₀) (h i).2⟩

end Conditions

/-! ### Stacks 082P -/

/-- The quotients of `Q_{F/X/Y}` have quasi-coherent quotient modules. -/
theorem isQuasicoherentOnSite_of_mem_quotients (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.quotients T) :
    (D.quotientModule T K).IsQuasicoherentOnSite :=
  hK.1

/-- **The sheaf property for the fpqc topology, reduced to the covering presieves.**  A
subfunctor of quotients whose condition makes the quotient modules quasi-coherent and descends
along every fpqc covering of a test scheme is a sheaf for the fpqc topology on the test schemes
over `Y`. -/
theorem quotientSubfunctor_isSheaf_fpqcTopology
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hQqc : ∀ (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)), K ∈ Q T →
      (D.quotientModule T K).IsQuasicoherentOnSite)
    (hdesc : ∀ {I : Type (u + 1)} {T : SchemesOver D.Y} {U : I → SchemesOver D.Y}
      (g : ∀ i, U i ⟶ T),
      IsFpqcCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) →
      ∀ K₀ : Subobject (D.baseChangeModule T), (D.quotientModule T K₀).IsQuasicoherentOnSite →
        (∀ i, D.quotientPullback (g i) K₀ ∈ Q (U i)) → K₀ ∈ Q T) :
    Presheaf.IsSheaf (fpqcTopology D.Y) (D.quotientSubfunctor Q hQ) := by
  rw [isSheaf_iff_isSheaf_of_type, fpqcTopology,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro T R hR
  obtain ⟨I, U, g, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  have hcov : IsFpqcCovering B S hS
      (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) :=
    represented_fpqc_family B S hS I (fun i ↦ (U i).left) (fun i ↦ (g i).left) hR
  exact D.isSheafFor_quotientSubfunctor Q hQ hQqc g hcov (hdesc g hcov)

/-- **Stacks 082P for `Q_{F/X/Y}`.**  The functor of quotients `Q_{F/X/Y} : (Sch/Y)ᵒᵖ ⥤ Sets`
of Stacks 082N satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P "the functor of quotients Q_{F/X/Y}"]
theorem quotientsFunctor_isSheaf_fpqcTopology :
    Presheaf.IsSheaf (fpqcTopology D.Y) D.quotientsFunctor := by
  rw [quotientsFunctor_eq_quotientSubfunctor]
  exact D.quotientSubfunctor_isSheaf_fpqcTopology _ _ D.isQuasicoherentOnSite_of_mem_quotients
    fun g hg K₀ hqc h ↦ D.mem_quotients_of_isFpqcCovering g hg K₀ hqc h

/-- **Stacks 082P for `Q^{fp}_{F/X/Y}`.**  The finite-presentation subfunctor of the functor of
quotients satisfies the sheaf property for the fpqc topology. -/
@[stacks 082P "the finite-presentation subfunctor Q^{fp}_{F/X/Y}"]
theorem finitePresentationQuotientsFunctor_isSheaf_fpqcTopology :
    Presheaf.IsSheaf (fpqcTopology D.Y) D.finitePresentationQuotientsFunctor := by
  rw [finitePresentationQuotientsFunctor_eq_quotientSubfunctor]
  exact D.quotientSubfunctor_isSheaf_fpqcTopology _ _
    (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1)
    fun g hg K₀ hqc h ↦ D.mem_finitePresentationQuotients_of_isFpqcCovering g hg K₀ hqc h

end QuotientSituation

/-! ### Stacks 09TT -/

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **Proper support of the quotient descends along an fpqc covering** of the test scheme, by
Stacks 0422 read through Stacks 07TZ and Stacks 0CZC. -/
theorem mem_properlySupportedQuotients_of_isFpqcCovering {I : Type v} {T : SchemesOver D.Y}
    {U : I → SchemesOver D.Y} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
    (K₀ : Subobject (D.baseChangeModule T))
    (hqc : (D.quotientModule T K₀).IsQuasicoherentOnSite)
    (h : ∀ i, D.quotientPullback (g i) K₀ ∈ D.properlySupportedQuotients (U i)) :
    K₀ ∈ D.properlySupportedQuotients T := by
  have hfp : K₀ ∈ D.finitePresentationQuotients T :=
    D.mem_finitePresentationQuotients_of_isFpqcCovering g hg K₀ hqc fun i ↦ (h i).1
  have := hfp.2
  refine ⟨hfp, hasProperSupport_of_isFpqcCovering B S hS (D.projection T)
    (D.isLocallyOfFiniteType_projection T) (fun i ↦ isPullback_baseChangeMap D.f (g i)) hg
    (D.quotientModule T K₀) hqc inferInstance fun i ↦ ?_⟩
  exact D.isProperlySupportedOver_of_iso (D.quotientPullbackCokernelIso (g i) K₀) (h i).2

/-- The Quot functor is the subfunctor of quotients cut out by its condition. -/
theorem quotFunctor_eq_quotientSubfunctor :
    D.quotFunctor = D.toQuotientSituation.quotientSubfunctor D.properlySupportedQuotients
      (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK) :=
  rfl

/-- **Stacks 09TT.**  In Situation 09TR, the Quot functor `Quot_{F/X/B} : (Sch/B)ᵒᵖ ⥤ Sets`
satisfies the sheaf property for the fpqc topology: for every fpqc covering `{T i ⟶ T}` of
schemes over `B`, a family of quotients of the `F_{T i}` — quasi-coherent, of finite
presentation, flat over `T i` and with support proper over `T i` — which agree on the overlaps
comes from a unique such quotient of `F_T`.

The topology is `AlgebraicGeometry.Space.fpqcTopology` on the test schemes over `B`.  The
proof is the source's: the functor of finitely presented quotients is an fpqc sheaf
(Stacks 082P, `…finitePresentationQuotientsFunctor_isSheaf_fpqcTopology`), and the condition of
proper support descends along fpqc coverings of the test scheme
(`AlgebraicGeometry.Space.QuotSituation.mem_properlySupportedQuotients_of_isFpqcCovering`). -/
@[stacks 09TT]
theorem quotFunctor_isSheaf_fpqcTopology :
    Presheaf.IsSheaf (fpqcTopology D.Y) D.quotFunctor := by
  rw [quotFunctor_eq_quotientSubfunctor]
  exact D.toQuotientSituation.quotientSubfunctor_isSheaf_fpqcTopology _ _
    (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1.1)
    fun g hg K₀ hqc h ↦ D.mem_properlySupportedQuotients_of_isFpqcCovering g hg K₀ hqc h

end QuotSituation

/-! ### The presheaf of pairs on the big fppf site of `S` -/

/-- **The fppf topology of the big fppf site of `S` is coarser than its fpqc topology.**  A
covering sieve of the fppf topology contains a flat, locally of finite presentation, jointly
surjective family, which is an fppf covering family of the underlying schemes and hence an fpqc
one. -/
@[sga "3 IV 6.3" "special case"]
theorem bigFppfOver_topology_le_fpqcTopology :
    BigFppfOver.topology B S hS ≤
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck := by
  intro U R hR
  obtain ⟨I, W, m, hmR, hflat, hlfp, hsurj⟩ := exists_family_of_mem_topology B S hS hR
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck (R := Presieve.ofArrows
      (fun i ↦ (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS))
      (fun i ↦ (Over.homMk (m i) : Over.mk (m i ≫ U.hom) ⟶ U))) ?_)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact hmR i
  · rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ?_
    rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨hsurj, fun i ↦ ⟨hflat i, hlfp i⟩⟩

/-- A presheaf of types on the big fppf site of `S` which is an fpqc sheaf is an fppf sheaf. -/
private theorem isSheaf_fppf_of_isSheaf_fpqc {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (h : Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) P) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) P := by
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  exact Presieve.isSheaf_of_le _ bigFppfOver_topology_le_fpqcTopology h

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- Two equal elements of the total presheaf have kernels which agree up to the transport along
an equality of the structure morphisms they are read at. -/
theorem TotalQuotient.kerAt_eq_cast_kerAt
    {Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T))}
    {U : BigFppfOver B S hS} {q q' : D.TotalQuotient Q U} (hq : q = q')
    {h₁ h₂ : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y} (e₁ : q'.hom = h₁) (e₂ : q.hom = h₂)
    (E : h₁ = h₂) :
    q.kerAt e₂ =
      cast (congrArg (fun k ↦ Subobject (D.baseChangeModule (D.testAt k))) E) (q'.kerAt e₁) := by
  subst hq
  subst E
  rfl

/-- The pullback of a quotient along a morphism of test schemes `homMk k e` whose source carries
a structure morphism only propositionally equal to the composite is the transport of the pullback
along `testAtMap k h`. -/
theorem quotientPullback_homMk_eq_cast {V W : BigFppfOver B S hS} (k : V ⟶ W)
    (h : (schemeSpaceFunctor B S hS).obj W ⟶ D.Y) (K : Subobject (D.baseChangeModule (D.testAt h)))
    {h₂ : (schemeSpaceFunctor B S hS).obj V ⟶ D.Y}
    (e : (schemeSpaceFunctor B S hS).map k ≫ h = h₂) :
    D.quotientPullback (CostructuredArrow.homMk k e : D.testAt h₂ ⟶ D.testAt h) K =
      cast (congrArg (fun k' ↦ Subobject (D.baseChangeModule (D.testAt k'))) e)
        (D.quotientPullback (D.testAtMap k h) K) := by
  subst e
  rfl

/-- **The total presheaf of a condition descending along fpqc coverings is an fpqc sheaf** on
the big fppf site of `S`.  This is
`AlgebraicGeometry.Space.QuotientSituation.isSheaf_totalQuotientFunctor` for the fpqc topology: the
structure morphisms glue because `Y` is an fpqc sheaf (Stacks 0APL), and the quotients then all
live over restrictions of one test scheme, where they glue by
`AlgebraicGeometry.Space.QuotientSituation.exists_quotientPullback_eq_of_isFpqcCovering`. -/
theorem isSheaf_fpqc_totalQuotientFunctor (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hQqc : ∀ (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)), K ∈ Q T →
      (D.quotientModule T K).IsQuasicoherentOnSite)
    (hdesc : ∀ {I : Type (u + 1)} {T : SchemesOver D.Y} {U : I → SchemesOver D.Y}
      (g : ∀ i, U i ⟶ T),
      IsFpqcCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) →
      ∀ K₀ : Subobject (D.baseChangeModule T), (D.quotientModule T K₀).IsQuasicoherentOnSite →
        (∀ i, D.quotientPullback (g i) K₀ ∈ Q (U i)) → K₀ ∈ Q T) :
    Presheaf.IsSheaf ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck)
      (D.totalQuotientFunctor hc Q hQ) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro U R hR
  obtain ⟨I, V, g, rfl⟩ := R.exists_eq_ofArrows
  have hRmem := hR
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  have hcov : IsFpqcCovering B S hS fun i ↦ yoneda.map (g i) :=
    represented_fpqc_family B S hS I V g hR
  intro x hx
  -- The structure morphisms glue: `Y` is an fpqc sheaf.
  have hY : Presieve.IsSheafFor D.Y.obj (Presieve.ofArrows V g) :=
    Presieve.IsSheaf.isSheafFor_of_mem_precoverage
      ((isSheaf_iff_isSheaf_of_type _ _).1 D.Y.property.isSheaf_fpqc) hRmem
  have hycomp : Presieve.FamilyOfElements.Compatible
      (fun ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ U) (hk : Presieve.ofArrows V g k) ↦
        yonedaEquiv (x k hk).hom.hom) := by
    intro W₁ W₂ W f₁ f₂ k₁ k₂ h₁ h₂ hw
    exact (yonedaEquiv_naturality (x k₁ h₁).hom.hom f₁).trans
      ((congrArg (fun q ↦ yonedaEquiv (TotalQuotient.hom q).hom) (hx f₁ f₂ h₁ h₂ hw)).trans
        (yonedaEquiv_naturality (x k₂ h₂).hom.hom f₂).symm)
  obtain ⟨y, hy, hyu⟩ := hY _ hycomp
  set hU : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y := ObjectProperty.homMk (yonedaEquiv.symm y)
    with hUdef
  have hgh : ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ U) (hk : Presieve.ofArrows V g k),
      (x k hk).hom = (schemeSpaceFunctor B S hS).map k ≫ hU := by
    intro W k hk
    refine ObjectProperty.hom_ext _ ?_
    have e : ((schemeSpaceFunctor B S hS).map k ≫ hU).hom =
        yonedaEquiv.symm (D.Y.obj.map k.op y) :=
      yonedaEquiv_symm_naturality_left k D.Y.obj y
    rw [e, hy k hk]
    exact (Equiv.symm_apply_apply yonedaEquiv (x k hk).hom.hom).symm
  -- The quotients over the restrictions of the single test scheme `(U, hU)`.
  have hKmem : ∀ i, (x (g i) (Presieve.ofArrows.mk i)).kerAt (hgh (g i) (Presieve.ofArrows.mk i))
      ∈ Q (D.testAtRestrict (g i) hU) := fun i ↦
    (x (g i) (Presieve.ofArrows.mk i)).kerAt_mem _
  have hcov' : IsFpqcCovering B S hS fun i ↦
      ((schemeSpaceFunctor B S hS).map (D.testAtMap (g i) hU).left).hom := hcov
  have hcompat : ∀ i j,
      D.quotientPullback (D.toHomSituation.overlapTestFst (D.testAtMap (g i) hU)
        (D.testAtMap (g j) hU))
          ((x (g i) (Presieve.ofArrows.mk i)).kerAt (hgh (g i) (Presieve.ofArrows.mk i))) =
      D.quotientPullback (D.toHomSituation.overlapTestSnd (D.testAtMap (g i) hU)
        (D.testAtMap (g j) hU))
          ((x (g j) (Presieve.ofArrows.mk j)).kerAt (hgh (g j) (Presieve.ofArrows.mk j))) := by
    intro i j
    have hxij := hx (pullback.fst (g i) (g j)) (pullback.snd (g i) (g j))
      (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j) pullback.condition
    have hL := D.quotientPullback_kerAt hc Q hQ (pullback.fst (g i) (g j))
      (x (g i) (Presieve.ofArrows.mk i)) (hgh (g i) (Presieve.ofArrows.mk i))
    have hR' := D.quotientPullback_kerAt hc Q hQ (pullback.snd (g i) (g j))
      (x (g j) (Presieve.ofArrows.mk j)) (hgh (g j) (Presieve.ofArrows.mk j))
    have hO := D.quotientPullback_homMk_eq_cast (pullback.snd (g i) (g j))
      ((schemeSpaceFunctor B S hS).map (g j) ≫ hU)
      ((x (g j) (Presieve.ofArrows.mk j)).kerAt (hgh (g j) (Presieve.ofArrows.mk j)))
      (h₂ := (schemeSpaceFunctor B S hS).map (pullback.fst (g i) (g j)) ≫
        (schemeSpaceFunctor B S hS).map (g i) ≫ hU)
      ((D.toHomSituation.overlapTestSnd (D.testAtMap (g i) hU) (D.testAtMap (g j) hU)).w)
    refine hL.trans (Eq.trans ?_ hO.symm)
    rw [hR']
    exact TotalQuotient.kerAt_eq_cast_kerAt D hxij _ _
      (D.toHomSituation.overlapTestSnd (D.testAtMap (g i) hU) (D.testAtMap (g j) hU)).w
  obtain ⟨K₀, hK₀qc, hK₀⟩ := D.exists_quotientPullback_eq_of_isFpqcCovering
    (fun i ↦ D.testAtMap (g i) hU) hcov'
    (fun i ↦ (x (g i) (Presieve.ofArrows.mk i)).kerAt (hgh (g i) (Presieve.ofArrows.mk i)))
    (fun i ↦ hQqc _ _ (hKmem i)) hcompat
  have hK₀mem : K₀ ∈ Q (D.testAt hU) :=
    hdesc (fun i ↦ D.testAtMap (g i) hU) hcov' K₀ hK₀qc fun i ↦ (hK₀ i).symm ▸ hKmem i
  refine ⟨⟨hU, K₀, hK₀mem⟩, ?_, fun t ht ↦ ?_⟩
  · rintro _ _ ⟨i⟩
    exact TotalQuotient.mk_eq (x (g i) _) (hgh (g i) _) _ (hK₀ i)
  · have hth : t.hom = hU := by
      refine ObjectProperty.hom_ext _ ?_
      have hya : yonedaEquiv t.hom.hom = y :=
        hyu _ fun W k hk ↦ (yonedaEquiv_naturality t.hom.hom k).trans
          (congrArg (fun q ↦ yonedaEquiv (TotalQuotient.hom q).hom) (ht k hk))
      exact (Equiv.symm_apply_apply yonedaEquiv t.hom.hom).symm.trans
        (congrArg yonedaEquiv.symm hya)
    refine (TotalQuotient.mk_eq t hth hK₀mem ?_).symm
    refine (D.eq_of_quotientPullback_eq_of_isFpqcCovering (fun i ↦ D.testAtMap (g i) hU) hcov'
      fun i ↦ ?_).symm
    exact ((D.quotientPullback_kerAt hc Q hQ (g i) t hth).trans
      (TotalQuotient.kerAt_congr (ht (g i) (Presieve.ofArrows.mk i)) _ _)).trans (hK₀ i).symm

/-! ### The two hypotheses of the reduction of Stacks 082P, discharged -/

/-- **The separatedness of quotients along fppf coverings, from the sheaf property of the total
presheaf.**  If the total presheaf of `Q` is an fppf sheaf, two quotients over a test scheme
which agree after pullback along a covering sieve are equal: the two pairs they make have equal
restrictions, hence are equal. -/
theorem quotientsSeparatedForCoverings_of_isSheaf (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.totalQuotientFunctor hc Q hQ)) :
    D.QuotientsSeparatedForCoverings Q := by
  intro U h R hR K₀ K₁ hK₀ hK₁ hagree
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 hsh) R hR
  have heq : (⟨h, K₀, hK₀⟩ : D.TotalQuotient Q U) = ⟨h, K₁, hK₁⟩ := by
    refine hs.isSeparatedFor
      (fun V g _ ↦ (D.totalQuotientFunctor hc Q hQ).map g.op ⟨h, K₀, hK₀⟩) _ _
      (fun V g _ ↦ rfl) (fun V g hg ↦ ?_)
    exact TotalQuotient.mk_eq_mk (hagree V g hg).symm _ _
  exact TotalQuotient.kerAt_congr heq rfl rfl

/-- **The glueing of quotients along fppf coverings, from the sheaf property of the total
presheaf.**  If the total presheaf of `Q` is an fppf sheaf, a family of quotients over the
restrictions of a test scheme `(U, h)` to the members of a covering sieve, compatible under
further pullback, is the family of pullbacks of one quotient over `(U, h)`: the pairs it makes
are a compatible family, whose amalgamation lies over `h` because `Y` is an fppf sheaf. -/
theorem quotientsGlueAlongCoverings_of_isSheaf (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.totalQuotientFunctor hc Q hQ)) :
    D.QuotientsGlueAlongCoverings Q := by
  intro U h R hR K hKmem hKcomp
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 hsh) R hR
  let x : Presieve.FamilyOfElements (D.totalQuotientFunctor hc Q hQ) R.arrows :=
    fun V g hg ↦ ⟨(schemeSpaceFunctor B S hS).map g ≫ h, K V g hg, hKmem V g hg⟩
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W V g k hg
    exact (TotalQuotient.mk_eq_mk (hKcomp V W k g hg) _ _).symm
  obtain ⟨t, ht, -⟩ := hs x hx
  have hY := ((isSheaf_iff_isSheaf_of_type _ _).1 D.Y.property.isSheaf) R hR
  have hth : t.hom = h := by
    refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
    refine hY.isSeparatedFor
      (fun V g _ ↦ D.Y.obj.map g.op (yonedaEquiv h.hom)) _ _ (fun V g hg ↦ ?_)
      (fun V g _ ↦ rfl)
    exact (yonedaEquiv_naturality t.hom.hom g).trans
      (congrArg (fun q ↦ yonedaEquiv (TotalQuotient.hom q).hom) (ht g hg)) |>.trans
        (yonedaEquiv_naturality h.hom g).symm
  refine ⟨t.kerAt hth, t.kerAt_mem hth, fun V g hg ↦ ?_⟩
  exact (D.quotientPullback_kerAt hc Q hQ g t hth).trans
    (TotalQuotient.kerAt_congr (ht g hg) _ rfl)

/-- The total presheaf of a condition descending along fpqc coverings is an fppf sheaf. -/
theorem isSheaf_fppf_totalQuotientFunctor (hc : ModulePushforwardCoherence B S hS)
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hQqc : ∀ (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)), K ∈ Q T →
      (D.quotientModule T K).IsQuasicoherentOnSite)
    (hdesc : ∀ {I : Type (u + 1)} {T : SchemesOver D.Y} {U : I → SchemesOver D.Y}
      (g : ∀ i, U i ⟶ T),
      IsFpqcCovering B S hS (fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom) →
      ∀ K₀ : Subobject (D.baseChangeModule T), (D.quotientModule T K₀).IsQuasicoherentOnSite →
        (∀ i, D.quotientPullback (g i) K₀ ∈ Q (U i)) → K₀ ∈ Q T) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (D.totalQuotientFunctor hc Q hQ) :=
  isSheaf_fppf_of_isSheaf_fpqc (D.isSheaf_fpqc_totalQuotientFunctor hc Q hQ hQqc hdesc)

/-- **The separatedness hypothesis of Stacks 082P holds for `Q_{F/X/Y}`.** -/
theorem quotientsSeparatedForCoverings_quotients :
    D.QuotientsSeparatedForCoverings D.quotients :=
  D.quotientsSeparatedForCoverings_of_isSheaf (modulePushforwardCoherence B S hS) D.quotients
    (fun m K hK ↦ D.quotientPullback_mem_quotients' m K hK)
    (D.isSheaf_fppf_totalQuotientFunctor _ _ _ D.isQuasicoherentOnSite_of_mem_quotients
      fun g hg K₀ hqc h ↦ D.mem_quotients_of_isFpqcCovering g hg K₀ hqc h)

/-- **The glueing hypothesis of Stacks 082P holds for `Q_{F/X/Y}`.** -/
theorem quotientsGlueAlongCoverings_quotients :
    D.QuotientsGlueAlongCoverings D.quotients :=
  D.quotientsGlueAlongCoverings_of_isSheaf (modulePushforwardCoherence B S hS) D.quotients
    (fun m K hK ↦ D.quotientPullback_mem_quotients' m K hK)
    (D.isSheaf_fppf_totalQuotientFunctor _ _ _ D.isQuasicoherentOnSite_of_mem_quotients
      fun g hg K₀ hqc h ↦ D.mem_quotients_of_isFpqcCovering g hg K₀ hqc h)

/-- **The separatedness hypothesis of Stacks 082P holds for `Q^{fp}_{F/X/Y}`.** -/
theorem quotientsSeparatedForCoverings_finitePresentationQuotients :
    D.QuotientsSeparatedForCoverings D.finitePresentationQuotients :=
  D.quotientsSeparatedForCoverings_of_isSheaf (modulePushforwardCoherence B S hS)
    D.finitePresentationQuotients
    (fun m K hK ↦ D.quotientPullback_mem_finitePresentationQuotients m K hK)
    (D.isSheaf_fppf_totalQuotientFunctor _ _ _
      (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1)
      fun g hg K₀ hqc h ↦ D.mem_finitePresentationQuotients_of_isFpqcCovering g hg K₀ hqc h)

/-- **The glueing hypothesis of Stacks 082P holds for `Q^{fp}_{F/X/Y}`.** -/
theorem quotientsGlueAlongCoverings_finitePresentationQuotients :
    D.QuotientsGlueAlongCoverings D.finitePresentationQuotients :=
  D.quotientsGlueAlongCoverings_of_isSheaf (modulePushforwardCoherence B S hS)
    D.finitePresentationQuotients
    (fun m K hK ↦ D.quotientPullback_mem_finitePresentationQuotients m K hK)
    (D.isSheaf_fppf_totalQuotientFunctor _ _ _
      (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1)
      fun g hg K₀ hqc h ↦ D.mem_finitePresentationQuotients_of_isFpqcCovering g hg K₀ hqc h)

end QuotientSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The separatedness hypothesis of Stacks 09TT holds**: the hypothesis `hsep` of
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf` is a theorem. -/
theorem quotientsSeparatedForCoverings_properlySupportedQuotients :
    D.QuotientsSeparatedForCoverings D.properlySupportedQuotients :=
  D.toQuotientSituation.quotientsSeparatedForCoverings_of_isSheaf
    (modulePushforwardCoherence B S hS) D.properlySupportedQuotients
    (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK)
    (D.toQuotientSituation.isSheaf_fppf_totalQuotientFunctor _ _ _
      (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1.1)
      fun g hg K₀ hqc h ↦ D.mem_properlySupportedQuotients_of_isFpqcCovering g hg K₀ hqc h)

/-- **The glueing hypothesis of Stacks 09TT holds**: the hypothesis `hglue` of
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf` is a theorem. -/
theorem quotientsGlueAlongCoverings_properlySupportedQuotients :
    D.QuotientsGlueAlongCoverings D.properlySupportedQuotients :=
  D.toQuotientSituation.quotientsGlueAlongCoverings_of_isSheaf
    (modulePushforwardCoherence B S hS) D.properlySupportedQuotients
    (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK)
    (D.toQuotientSituation.isSheaf_fppf_totalQuotientFunctor _ _ _
      (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1.1)
      fun g hg K₀ hqc h ↦ D.mem_properlySupportedQuotients_of_isFpqcCovering g hg K₀ hqc h)

end QuotSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **Stacks 09TT, for the presheaf of pairs on the big fppf site of `S`.**  The source also
reads `Quot_{F/X/B}` as a functor on the schemes over `S` with a morphism to `B`: its value at
`T` is the set of pairs `(h : T ⟶ B, Q)` with `Q` a member of `Quot_{F/X/B}(T)` for the test
scheme `(T, h)`.  That presheaf, `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`,
satisfies the sheaf property for the fpqc topology of the big fppf site of `S`. -/
@[stacks 09TT "the Quot functor read on the schemes over S together with its morphism to B"]
theorem quotSitePresheaf_isSheaf_fpqc :
    Presheaf.IsSheaf ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck)
      D.quotSitePresheaf :=
  (Presheaf.isSheaf_of_iso_iff D.quotSitePresheafIsoTotal).2
    (D.toQuotientSituation.isSheaf_fpqc_totalQuotientFunctor (modulePushforwardCoherence B S hS)
      D.properlySupportedQuotients
      (fun m K hK ↦ D.quotientPullback_mem_properlySupportedQuotients m K hK)
      (fun T K hK ↦ D.isQuasicoherentOnSite_of_mem_quotients T K hK.1.1)
      fun g hg K₀ hqc h ↦ D.mem_properlySupportedQuotients_of_isFpqcCovering g hg K₀ hqc h)

/-- **The Quot presheaf of Stacks 09TR is an fppf sheaf** on the big fppf site of `S`, with no
hypothesis: the fppf topology is coarser than the fpqc topology, for which this is
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fpqc`.  This is the sheaf
property Stacks 09TU consumes; it discharges the two hypotheses of
`AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf`. -/
theorem quotSitePresheaf_isSheaf_fppf :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) D.quotSitePresheaf :=
  isSheaf_fppf_of_isSheaf_fpqc D.quotSitePresheaf_isSheaf_fpqc

/-- **Stacks 09TT.**  The Quot functor `Quot_{F/X/B}` of Stacks 09TR, read as a presheaf on the
schemes of the big fppf site of `S`, satisfies the sheaf condition for the fppf topology of that
site: a compatible family, for an fppf covering of a scheme `T` of the site, of pairs consisting
of a morphism to `B` and a quotient of the corresponding pullback of `F` which is quasi-coherent,
of finite presentation, flat over the member and with support proper over it, comes from a
unique such pair over `T`.

This name is an alias of `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fppf`,
which has no hypothesis: the separatedness and glueing of quotients along a covering of a test
scheme are the theorems
`AlgebraicGeometry.Space.QuotSituation.quotientsSeparatedForCoverings_properlySupportedQuotients`
and `…quotientsGlueAlongCoverings_properlySupportedQuotients`, and the sheaf property is
deduced from the fpqc one, `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf_isSheaf_fpqc`,
as the fppf topology of the site is coarser than its fpqc topology. -/
@[stacks 09TT "the fppf sheaf property of the Quot presheaf of pairs on the big fppf site over \
S, unconditionally; it is the consequence, for the coarser fppf topology, of the source's fpqc \
statement, which is `quotSitePresheaf_isSheaf_fpqc`. This name is an alias of \
`quotSitePresheaf_isSheaf_fppf`."]
alias quotSitePresheaf_isSheaf := quotSitePresheaf_isSheaf_fppf

end QuotSituation

end AlgebraicGeometry.Space

end
