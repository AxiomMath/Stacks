module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RestrictScalarsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RingShriekCover
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage

/-!
# Constructibility over a finite ring is detected after restriction of scalars

Let `ρ : R →+* Λ` be a ring homomorphism with `R` Noetherian and `Λ` finite, not necessarily
commutative, and let `X` be a quasi-compact and quasi-separated scheme of a big étale site. A sheaf
`G` of `Λ`-modules on `X_étale` whose restriction of scalars to `R` is a constructible sheaf of
`R`-modules is a constructible sheaf of `Λ`-modules.

With `R = ℤ/n` and `n` the characteristic of `Λ`, this is how constructibility statements proved
for the commutative coefficient ring `ℤ/n` — Tag 0GL0 for instance — are read for the finite,
possibly noncommutative, coefficient rings of the trace formula (Tag 03SZ).

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_restrictScalars`:
  a sheaf of `Λ`-modules whose restriction of scalars along `ρ` is constructible is constructible.

## Proof

The class `𝒞` of sheaves of `Λ`-modules whose restriction of scalars is constructible is a weak
Serre class, restriction of scalars being exact. It contains the generators
`j_{U!}\underline{\Lambda}_U` at quasi-compact quasi-separated étale objects (they are
constructible over `Λ`, `AlgebraicGeometry.isConstructibleModuleSheaf_restrictScalars`). For `F`
in `𝒞`, the finite generation step of Tag 095P,
`AlgebraicGeometry.exists_finset_epi_sigma_desc_of_isFG_of_isConstructible`, applies to any
epimorphism onto `F` from a sum of generators (Tag 093B): the stalks of `F` are finite sets, and
the loci where a cokernel in `𝒞` has a nonzero stalk are constructible (Tag 09YS over `R`). So
`G` is a quotient of a finite sum `P` of generators, and so is the kernel of `P ↠ G`, which lies in
`𝒞`: `G` is the cokernel of a map between finite sums of generators, which are constructible over
`Λ`, and is constructible over `Λ` by Tag 03RZ (3).

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance high] hasWeakSheafify_over_moduleCat_type
  isRightAdjoint_smallEtalePushforward_moduleCat_type

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {R Λ : Type} [Ring R] [Ring Λ] (ρ : R →+* Λ)

/-- Restriction of scalars along `ρ`, on sheaves of modules on the small étale site of Tag 021B. -/
abbrev smallEtaleRestrictScalars :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R) :=
  sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)

/-- Restriction of scalars is left adjoint to coextension of scalars on the small étale site of
Tag 021B: the sectionwise adjunction, restricted to sheaves. -/
def smallEtaleRestrictCoextendScalarsAdj :
    smallEtaleRestrictScalars B X ρ ⊣
      sheafCompose (SmallEtale.topology B X.obj X.property)
        (ModuleCat.coextendScalars ρ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} Λ) :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).whiskerRight
      (SmallEtale B X.obj X.property)ᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- Restriction of scalars on sheaves of modules on the small étale site is a left adjoint. -/
instance smallEtaleRestrictScalars_isLeftAdjoint :
    (smallEtaleRestrictScalars B X ρ).IsLeftAdjoint :=
  (smallEtaleRestrictCoextendScalarsAdj B X ρ).isLeftAdjoint

/-- Restriction of scalars on sheaves of modules on the small étale site preserves finite
colimits. -/
instance smallEtaleRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleRestrictScalars B X ρ) := inferInstance

/-- Restriction of scalars on sheaves of modules on the small étale site preserves finite
limits. -/
instance smallEtaleRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleRestrictScalars B X ρ) := by
  have := Stacks.ModuleSheaf.hasSheafCompose_restrictScalars_of_ring.{u + 1}
    (SmallEtale.topology B X.obj X.property) ρ
  infer_instance

/-- Restriction of scalars on sheaves of modules on the small étale site is additive. -/
instance smallEtaleRestrictScalars_additive : (smallEtaleRestrictScalars B X ρ).Additive where
  map_add := rfl

/-- **The étale stalk commutes with restriction of scalars.** -/
def etaleStalkRestrictScalarsIso (t : GeometricPoint X.obj)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    etaleStalk B X.obj X.property t ((smallEtaleRestrictScalars B X ρ).obj G).obj ≅
      (ModuleCat.restrictScalars.{u + 1} ρ).obj (etaleStalk B X.obj X.property t G.obj) :=
  haveI : PreservesColimitsOfSize.{u, u + 1} (ModuleCat.restrictScalars.{u + 1} ρ) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} ρ).leftAdjoint_preservesColimits
  (preservesColimitIso (ModuleCat.restrictScalars.{u + 1} ρ)
    ((CategoryOfElements.π (geometricPointFiber B X.obj X.property t)).op ⋙ G.obj)).symm

/-- **Constructibility over a finite ring is detected after restriction of scalars.** Let
`ρ : R →+* Λ` be a homomorphism of finite rings, `R` Noetherian, `Λ` not necessarily commutative,
and `X` a quasi-compact quasi-separated scheme of a big étale site. A sheaf of `Λ`-modules on
`X_étale` whose restriction of scalars along `ρ` is a constructible sheaf of `R`-modules is a
constructible sheaf of `Λ`-modules. -/
theorem isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_restrictScalars
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [IsNoetherianRing R] [Finite R] [Finite Λ]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleModuleSheaf B X R ((smallEtaleRestrictScalars B X ρ).obj G)) :
    IsConstructibleModuleSheaf B X Λ G := by
  classical
  have : IsNoetherianRing Λ := isNoetherian_of_finite Λ Λ
  have : HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) :=
    SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  have : HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} R) :=
    SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X R
  let φ := smallEtaleRestrictScalars B X ρ
  let PR := isConstructibleModuleSheafProperty.{u, u + 1, 0} B X R
  have : PR.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} B X R
  let PΛ := isConstructibleModuleSheafProperty.{u, u + 1, 0} B X Λ
  have : PΛ.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, 0, 0} B X Λ
  let C : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :=
    PR.inverseImage φ
  have : C.IsWeakSerreClass := inferInstance
  have hgenΛ : ∀ U : SmallEtale B X.obj X.property, IsQCQSEtaleObject B X U →
      PΛ (moduleShriekConstant.{u, 0, 0} B X Λ U) := fun U hU => by
    have hc : CompactSpace U.obj.left.obj := hU.1
    have hq : QuasiSeparatedSpace U.obj.left.obj := hU.2
    exact isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ
      (isConstructibleFlatModuleSheaf_moduleShriekConstant_of_ring B X Λ U)
  have hgenC : ∀ U : SmallEtale B X.obj X.property, IsQCQSEtaleObject B X U →
      C (moduleShriekConstant.{u, 0, 0} B X Λ U) := fun U hU =>
    isConstructibleModuleSheaf_restrictScalars B ρ X _ (hgenΛ U hU)
  have hclosedC : C.IsClosedUnderFiniteCoproducts :=
    Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass _
  have hclosedΛ : PΛ.IsClosedUnderFiniteCoproducts :=
    Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass _
  have hwlb : ∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        (ModuleCat.{u + 1} R) := fun Z V =>
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, 0, 0}
      ((SmallEtale.topology B Z.obj Z.property).over V) R
  have := preservesFilteredColimits_forget_moduleCatMax_of_ring.{u, 0} R
  have key : ∀ F, C F → ∃ (n : ℕ) (V : Fin n → SmallEtale B X.obj X.property),
      (∀ i, IsQCQSEtaleObject B X (V i)) ∧
        ∃ p : (∐ fun i => moduleShriekConstant.{u, 0, 0} B X Λ (V i)) ⟶ F, Epi p := by
    intro F hF
    obtain ⟨A, U, hU, q, hq⟩ := exists_epi_sigma_moduleShriekConstant_qcqs_of_ring B X Λ F
    have hfg : ∀ t : GeometricPoint X.obj, ModuleCat.isFG Λ
        (((geometricPointSitePoint B X.obj X.property t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) := by
      intro t
      have h1 : ModuleCat.isFG R ((etaleModuleStalkFunctor.{u, u + 1, 0} B X R t).obj (φ.obj F)) :=
        stalk_prop_of_isStratifiedLocallyConstantWith B X R (ModuleCat.isFG R)
          (fun {E E'} e hE => by
            rw [ModuleCat.isFG_iff] at hE ⊢
            exact Module.Finite.equiv e.toLinearEquiv)
          (fun E hE => by
            rw [ModuleCat.isFG_iff]
            exact Module.Finite.of_finite)
          (φ.obj F) hF t
      rw [ModuleCat.isFG_iff] at h1 ⊢
      have h1' : Finite ((etaleModuleStalkFunctor.{u, u + 1, 0} B X R t).obj (φ.obj F)) :=
        Module.finite_of_finite R
      have : Finite (((geometricPointSitePoint B X.obj X.property t).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj F) :=
        @Finite.of_equiv _ _ h1' (etaleStalkRestrictScalarsIso B X ρ t F).toLinearEquiv.toEquiv
      exact Module.Finite.of_finite
    have hcons : ∀ s : Finset (Discrete A), Topology.IsConstructible
        {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
          ¬ IsZero (etaleStalk B X.obj X.property t
            (cokernel ((Sigma.desc fun a : {a // a ∈ s} =>
              Sigma.ι (fun a => moduleShriekConstant.{u, 0, 0} B X Λ (U a)) a.1.as) ≫
                q)).obj)} := by
      intro s
      let f := (Sigma.desc fun a : {a // a ∈ s} =>
        Sigma.ι (fun a => moduleShriekConstant.{u, 0, 0} B X Λ (U a)) a.1.as) ≫ q
      have hsum : C (∐ fun a : {a // a ∈ s} => moduleShriekConstant.{u, 0, 0} B X Λ (U a.1.as)) :=
        C.prop_coproduct fun a => hgenC _ (hU _)
      have hcok : C (cokernel f) := C.prop_cokernel f hsum hF
      have h := isConstructible_setOf_exists_geometricPoint_etaleStalk_of_ring.{u, 0, u + 1} B X R
        (φ.obj (cokernel f)) hcok (fun E => ¬ IsZero E) (fun e => not_congr e.isZero_iff)
      have hz : ∀ t : GeometricPoint X.obj,
          IsZero (etaleStalk B X.obj X.property t (cokernel f).obj) ↔
            IsZero (etaleStalk B X.obj X.property t (φ.obj (cokernel f)).obj) := fun t => by
        rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
        exact (Equiv.subsingleton_congr
          (etaleStalkRestrictScalarsIso B X ρ t (cokernel f)).toLinearEquiv.toEquiv).symm
      have hset : {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
            ¬ IsZero (etaleStalk B X.obj X.property t (cokernel f).obj)} =
          {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
            ¬ IsZero (etaleStalk B X.obj X.property t (φ.obj (cokernel f)).obj)} := by
        ext x
        exact exists_congr fun t => and_congr_right fun _ => not_congr (hz t)
      exact hset ▸ h
    have := hq
    obtain ⟨s, hs⟩ := exists_finset_epi_sigma_desc_of_isFG_of_isConstructible B X Λ F
      (fun a => moduleShriekConstant.{u, 0, 0} B X Λ (U a)) q hfg hcons
    refine ⟨s.card, fun i => U (s.equivFin.symm i).1.as, fun i => hU _,
      (Sigma.reindex s.equivFin.symm
          (fun a : {a // a ∈ s} =>
            moduleShriekConstant.{u, 0, 0} B X Λ (U a.1.as))).hom ≫
        ((Sigma.desc fun a : {a // a ∈ s} =>
          Sigma.ι (fun a => moduleShriekConstant.{u, 0, 0} B X Λ (U a)) a.1.as) ≫ q), ?_⟩
    have := hs
    infer_instance
  obtain ⟨n, V, hV, p, hp⟩ := key G hG
  have hPC : C (∐ fun i => moduleShriekConstant.{u, 0, 0} B X Λ (V i)) :=
    C.prop_coproduct fun i => hgenC _ (hV i)
  have hKC : C (kernel p) := C.prop_kernel p hPC hG
  obtain ⟨m, W, hW, q, hq⟩ := key (kernel p) hKC
  have hc : IsColimit (CokernelCofork.ofπ (f := q ≫ kernel.ι p) p (by simp)) :=
    isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) q rfl
  have hcokΛ : PΛ (cokernel (q ≫ kernel.ι p)) :=
    PΛ.prop_cokernel _ (PΛ.prop_coproduct fun i => hgenΛ _ (hW i))
      (PΛ.prop_coproduct fun i => hgenΛ _ (hV i))
  exact PΛ.prop_of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc) hcokΛ

end AlgebraicGeometry

end
