module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Colimits
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainCokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness

/-!
# Tag 06V4 on a restricted domain of algebras

[Stacks, Tag 06V4] — adequate module-valued functors are closed under arbitrary colimits — is
proved for the full domain of commutative `A`-algebras as
`AdequateFunctor.isAdequate_colimit`. This file carries it to a domain
`ι : C ⥤ CommAlgCat A` with a base algebra object on which the lifting property of
[Stacks, Tag 06V0] holds, then to the algebras of a site, and finally discharges
`Stacks.Adequate.AffineAdequateColimits`.

## Main results

* `AdequateFunctor.isAdequate_coproduct_on` — a direct sum of adequate module-valued functors on
  a restricted domain of algebras is adequate.
* `AdequateFunctor.isAdequate_colimit_on` — [Stacks, Tag 06V4] on a restricted domain of
  algebras, given a base algebra object and the lifting property of [Stacks, Tag 06V0] there.
* `AdequateFunctor.isAdequate_colimit_site` — [Stacks, Tag 06V4] over the algebras of a site.
* `Stacks.Adequate.affineAdequateColimits` — `Stacks.Adequate.AffineAdequateColimits` holds for
  every shape, i.e. [Stacks, Tag 06V4] on the site's domain of algebras.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06V4 is
`AdequateFunctor.isAdequate_coproduct` and `AdequateFunctor.isAdequate_colimit`, over all
commutative algebras, and these are that statement transported to a restricted domain. This is
the same convention as `AdequateFunctor.isAdequate_kernel_on` for 06V3 and
`AdequateFunctor.isAdequate_cokernel_on` for 06V2.

The transport is *not* the one used for [Stacks, Tag 06UX] in
`AdequateFunctor.exists_coproduct_linearlyAdequate_surjective_on`. There adequacy is a
hypothesis, so `AdequateFunctor.IsAdequate.exists_extension` may write the functor as the
restriction of an adequate functor on all algebras and let the general statement apply. Here
adequacy is the *conclusion*, and `exists_extension` is only an objectwise existence statement:
it does not lift a whole `J`-shaped diagram of functors on the domain to a `J`-shaped diagram on
all algebras, so the general 06V4 cannot be invoked. The proof of the source is therefore
reproduced on the restricted domain, which costs exactly three generic inputs —
exactness of coproducts of module-valued functors on the domain, preservation of colimits by
extension of scalars to the domain, and fullness of extension of scalars there — plus
[Stacks, Tag 06V2] on the domain for the final cokernel.

No shape hypothesis is needed. The reduction of a colimit to a cokernel of a map of two direct
sums is valid for an arbitrary index category, so neither filteredness nor finiteness of the
shape enters; the only constraint on the shape is the size constraint already present in the
source, namely that the shape and its morphisms live in the value universe, which is where the
direct sums indexed by it exist. [Stacks, Tag 06UU] — whose two `UnivLE` hypotheses pin other
work in this area to a single universe — plays no part: it concerns filtered colimits of
algebras in the *source* of a functor, not colimits of functors.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u u₁ v₁ u₃ v₃ m

namespace AdequateFunctor

section Domain

variable {A : Type u} [CommRing A] {C : Type u₁} [Category.{v₁} C]

/-- Extension of scalars to a restricted domain of algebras commutes with all colimits of any
shape admitted by abelian groups: it is extension of scalars on all algebras followed by
reindexing, and each of those preserves such colimits. -/
public instance moduleExtensionFunctorOn_preservesColimitsOfShape
    (ι : C ⥤ CommAlgCat.{max u v} A) (J : Type u₃) [Category.{v₃} J]
    [HasColimitsOfShape J AddCommGrpCat.{max u v w}] :
    PreservesColimitsOfShape J (moduleExtensionFunctorOn.{max u v w, v} ι) :=
  have _ : PreservesColimitsOfShape J
      (PresheafOfModules.pushforward₀.{max u v w} ι.op (algebraRingDiagram.{v} A)) :=
    pushforward₀_preservesColimitsOfShape.{max u v w} ι.op (algebraRingDiagram.{v} A) J
  comp_preservesColimitsOfShape _ _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the coproduct and AB4 instances across the universe levels `max u v w`
/-- Coproducts of module-valued functors on a restricted domain of algebras, indexed by a type in
the value universe, are exact: they are computed objectwise on the underlying presheaves of
abelian groups, where exactness is the corresponding Grothendieck axiom. -/
public lemma hasExactColimitsOfShape_moduleValuedFunctorOn (ι : C ⥤ CommAlgCat.{max u v} A)
    (K : Type w) :
    HasExactColimitsOfShape (Discrete K) (ModuleValuedFunctorOn.{max u v w, v} ι) :=
  let _ : AB4OfSize.{w} AddCommGrpCat.{max u v w} :=
    AB4OfSize_shrink.{w, max u v w} (C := AddCommGrpCat.{max u v w})
  let _ := AB4OfSize.ofShape (C := AddCommGrpCat.{max u v w}) K
  let _ : HasColimitsOfShape (Discrete K) AddCommGrpCat.{max u v w} :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{max u v, w})
  let _ : HasCoproducts.{w} AddCommGrpCat.{max u v w} :=
    hasCoproducts_shrink.{w, max u v} (C := AddCommGrpCat.{max u v w})
  let _ : HasCoproducts.{w} (Cᵒᵖᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :=
    fun _ => functorCategoryHasColimitsOfShape
  let _ : HasCoproducts.{w} (ModuleValuedFunctorOn.{max u v w, v} ι) :=
    fun _ => PresheafOfModules.hasColimitsOfShape _ _
  HasExactColimitsOfShape.domain_of_functor (Discrete K)
    (PresheafOfModules.toPresheaf.{max u v w} (algebraRingDiagramOn.{v} ι))

/-- Adequacy on a domain of algebras with a base object can equivalently be witnessed by any
morphism between module extensions: fullness of extension of scalars there supplies the
underlying map of modules. This is `AdequateFunctor.isAdequate_iff` on a restricted domain. -/
public lemma isAdequate_iff_on {ι : C ⥤ CommAlgCat.{max u v} A} (b : BaseAlgebraObject.{v} ι)
    (F : ModuleValuedFunctorOn.{max u v w, v} ι) :
    IsAdequate.{max u v w, v} ι F ↔
      ∃ (M N : ModuleCat.{max u v w} A)
        (f : (moduleExtensionFunctorOn.{max u v w, v} ι).obj M ⟶
          (moduleExtensionFunctorOn.{max u v w, v} ι).obj N), Nonempty (F ≅ kernel f) := by
  let e := presheafOfModulesUliftIso.{max u v, max u v w} (algebraRingDiagramOn.{v} ι) F
  constructor
  · rintro ⟨M, N, f, ⟨i⟩⟩
    exact ⟨M, N, (moduleExtensionFunctorOn.{max u v w, v} ι).map f, ⟨e.symm ≪≫ i⟩⟩
  · rintro ⟨M, N, f, ⟨i⟩⟩
    exact ⟨M, N, moduleHomOfExtensionNatTransOn.{max u v w} b f,
      ⟨e ≪≫ i ≪≫ kernelIsoOfEq (moduleExtension_natTransOn_eq_map.{max u v w} b f)⟩⟩

/-- A coproduct of adequate module-valued functors on a domain of algebras is adequate: each
summand is the restriction of an adequate functor on all algebras, reindexing preserves
coproducts, and a coproduct of adequate functors on all algebras is adequate. -/
public theorem isAdequate_coproduct_on {ι : C ⥤ CommAlgCat.{max u v} A}
    {J : Type (max u v w)} (L : J → ModuleValuedFunctorOn.{max u v w, v} ι)
    (hL : ∀ j, IsAdequate.{max u v w, v} ι (L j)) :
    IsAdequate.{max u v w, v} ι (∐ L) := by
  classical
  choose G hG eG using fun j => IsAdequate.exists_extension.{max u v w} ι (L j) (hL j)
  let R := AdequateFunctor.restrictDomain.{max u v w, v} ι (𝟭 (CommAlgCat.{max u v} A))
  have : PreservesColimitsOfShape (Discrete J) R :=
    pushforward₀_preservesColimitsOfShape.{max u v w} ι.op (algebraRingDiagram.{v} A) (Discrete J)
  refine (IsAdequate.restrictDomain.{max u v w, v} ι (𝟭 _) (∐ G)
    (isAdequate_coproduct G hG)).of_iso ?_
  let eD : Discrete.functor L ≅ Discrete.functor G ⋙ R :=
    Discrete.natIso fun j =>
      (presheafOfModulesUliftIso.{max u v, max u v w}
        (algebraRingDiagramOn.{v} ι) (L j.as)).symm ≪≫ (eG j.as).some
  exact HasColimit.isoOfNatIso eD ≪≫ (preservesColimitIso R (Discrete.functor G)).symm
/-- **Stacks Lemma 06V4 on a restricted domain of algebras.** A colimit of adequate module-valued
functors on a domain of algebras, over a shape in the value universe, is adequate, given a base
algebra object and the lifting property of [Stacks, Tag 06V0] on that domain.

The colimit is the cokernel of the difference of two maps between the direct sum over the
morphisms of the shape and the direct sum over its objects, both of which are adequate by
`AdequateFunctor.isAdequate_coproduct_on`; [Stacks, Tag 06V2] on the domain then makes the
cokernel adequate. -/
public lemma isAdequate_colimit_on {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι) (hlift : FiniteFreeKernelLifting.{w, v} ι)
    {J : Type (max u v w)} [Category.{max u v w} J]
    (F : J ⥤ ModuleValuedFunctorOn.{max u v w, v} ι)
    (hF : ∀ a, IsAdequate.{max u v w, v} ι (F.obj a)) :
    IsAdequate.{max u v w, v} ι (colimit F) := by
  let s : (∐ fun x : Σ p : J × J, p.1 ⟶ p.2 => F.obj x.1.1) ⟶ ∐ F.obj :=
    CategoryTheory.Limits.Sigma.desc fun x =>
      F.map x.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨x.1.2⟩
  let t : (∐ fun x : Σ p : J × J, p.1 ⟶ p.2 => F.obj x.1.1) ⟶ ∐ F.obj :=
    CategoryTheory.Limits.Sigma.desc fun x => colimit.ι (Discrete.functor F.obj) ⟨x.1.1⟩
  have hP : IsAdequate.{max u v w, v} ι (∐ F.obj) := isAdequate_coproduct_on.{w} F.obj hF
  have hQ : IsAdequate.{max u v w, v} ι
      (∐ fun x : Σ p : J × J, p.1 ⟶ p.2 => F.obj x.1.1) :=
    isAdequate_coproduct_on.{w} _ (fun _ => hF _)
  refine (isAdequate_cokernel_on.{w} b hlift (s - t) hQ hP).of_iso ?_
  refine (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)) ≪≫ ?_
  exact IsColimit.coconePointUniqueUpToIso
    (CategoryTheory.Preadditive.isColimitCokernelCoforkOfCofork
      (CategoryTheory.Limits.coequalizerIsCoequalizer s t))
    (CategoryTheory.Limits.colimit.isColimit (parallelPair (s - t) 0))

end Domain

/-! ### Tag 06V4 over the algebras of a site -/

section Site

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- **Stacks Lemma 06V4 over the algebras of a site.** A colimit of adequate module-valued
functors on the algebras whose spectra have size below the cutoff is adequate.

The two inputs of `AdequateFunctor.isAdequate_colimit_on` are the base ring as an object of the
site, `AdequateFunctor.BaseAlgebraObject.siteOfSpecMem`, and the lifting property of
[Stacks, Tag 06V0] there, `AdequateFunctor.finiteFreeKernelLifting_site`. -/
public theorem isAdequate_colimit_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    {J : Type (max u w)} [Category.{max u w} J]
    (F : J ⥤ ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)))
    (hF : ∀ a, IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (F.obj a)) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (colimit F) :=
  isAdequate_colimit_on.{w, u} (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA)
    (finiteFreeKernelLifting_site.{w} hκ hsl A hA) F hF

end Site

end AdequateFunctor

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- `Stacks.Adequate.AffineAdequateColimits` holds for every shape: adequacy of module-valued
functors on the algebras of the site over an affine scheme of the site is closed under colimits
of shape `J`. This is [Stacks, Tag 06V4] on the site's domain of algebras.

It is `AdequateFunctor.isAdequate_colimit_site`, whose two inputs are the same as those of
`Stacks.Adequate.affineAdequateKernels`: the base ring as an object of the site and the lifting
property of [Stacks, Tag 06V0] there. The shape carries no hypothesis. -/
public theorem affineAdequateColimits (J : Type (max u m)) [Category.{max u m} J] :
    AffineAdequateColimits.{u, m} B J := by
  intro A hA K c hc hK
  have hcol : HasColimit K := ⟨⟨c, hc⟩⟩
  refine (AdequateFunctor.isAdequate_colimit_site.{m}
    (lt_of_le_of_lt (Scheme.aleph0_le_size (Spec A)) hA)
    B.cutoff_isStrongPrelimit A hA K hK).of_iso ?_
  exact hc.coconePointUniqueUpToIso (colimit.isColimit K)

end Stacks.Adequate

end
