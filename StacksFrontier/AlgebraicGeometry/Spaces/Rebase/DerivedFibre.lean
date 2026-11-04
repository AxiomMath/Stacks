module

public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.DirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalize
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalizeEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.FinitePresentationOverFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.Derived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyQcqsEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardHigherDirectImages
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackOfIso


/-!
# Derived fibres along the change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and `Y` an algebraic space over `W`, with
lower-shriek extension `Λ_h Y` over `S`.  For an object `G` of `D(𝒪_{Λ_h Y})` and a field-valued
point `p : Spec(k) ⟶ Y`, the derived-fibre Betti numbers `dim_k H^n(G ⊗^𝐋 k)` of `G` at `p` read
over `S` are those of `Ψ G` at `p`, where `Ψ : D(𝒪_{Λ_h Y}) ⥤ D(𝒪_Y)` is restriction along the
equivalence of small étale sites.  Consequently the derived-fibre Euler characteristics of a
perfect `G` and of `Ψ G` agree under the bijection of points of Stacks 03I5.

## Main definitions

* `SemilinearEquivalent`: modules over two rings related by an additive isomorphism, semilinear
  along a ring isomorphism.
* `AlgebraicGeometry.Space.modulePushforwardEquivalenceOfIso`: direct image of modules along an
  isomorphism of algebraic spaces is an equivalence.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoMapDerivedOfIso`: `Lι^* ≅ (ι⁻¹)_*`.

## Main results

* `SemilinearEquivalent.finrank_restrictScalars_eq`: semilinearly equivalent modules have the same
  dimension over a common field of definition.
* `AlgebraicGeometry.Space.derivedFibreBettiAt_rebaseDerived`: the Betti numbers agree.
* `AlgebraicGeometry.Space.derivedFibreEuler_rebaseDerived`: the Euler characteristics agree.

## References

* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Two modules over possibly different rings are **semilinearly equivalent** when there are an
isomorphism of the rings and an additive isomorphism of the modules which is semilinear along
it. -/
def SemilinearEquivalent (R R' : Type*) [Semiring R] [Semiring R'] (M M' : Type*) [AddCommMonoid M]
    [AddCommMonoid M'] [Module R M] [Module R' M'] : Prop :=
  ∃ (ρ : R ≃+* R') (j : M ≃+ M'), ∀ (r : R) (m : M), j (r • m) = ρ r • j m

namespace SemilinearEquivalent

variable {R R' R'' : Type*} [Semiring R] [Semiring R'] [Semiring R''] {M M' M'' : Type*}
  [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M''] [Module R M] [Module R' M']
  [Module R'' M'']

/-- Linearly equivalent modules over the same ring are semilinearly equivalent. -/
theorem of_linearEquiv {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N'] [Module R N]
    [Module R N'] (e : N ≃ₗ[R] N') : SemilinearEquivalent R R N N' :=
  ⟨RingEquiv.refl R, e.toAddEquiv, fun r m => e.map_smul r m⟩

/-- Semilinear equivalence is symmetric. -/
theorem symm (h : SemilinearEquivalent R R' M M') : SemilinearEquivalent R' R M' M := by
  obtain ⟨ρ, j, hj⟩ := h
  refine ⟨ρ.symm, j.symm, fun r m => j.injective ?_⟩
  rw [AddEquiv.apply_symm_apply, hj, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Semilinear equivalence is transitive. -/
theorem trans (h : SemilinearEquivalent R R' M M') (h' : SemilinearEquivalent R' R'' M' M'') :
    SemilinearEquivalent R R'' M M'' := by
  obtain ⟨ρ, j, hj⟩ := h
  obtain ⟨ρ', j', hj'⟩ := h'
  exact ⟨ρ.trans ρ', j.trans j', fun r m => by simp [hj, hj']⟩

/-- **Semilinearly equivalent modules have the same dimension over a common field of
definition**: if `k` maps isomorphically to both rings, the two modules read over `k` have the
same dimension, whatever the isomorphism of the rings. -/
theorem finrank_restrictScalars_eq {k R R' : Type u} [Field k] [Ring R] [Ring R']
    (f : k →+* R) (f' : k →+* R') (hf : Function.Bijective f) (hf' : Function.Bijective f')
    {M : ModuleCat.{u} R} {M' : ModuleCat.{u} R'} (h : SemilinearEquivalent R R' M M') :
    Module.finrank k ((ModuleCat.restrictScalars f).obj M) =
      Module.finrank k ((ModuleCat.restrictScalars f').obj M') := by
  obtain ⟨ρ, j, hj⟩ := h
  let e' := RingEquiv.ofBijective f' hf'
  let i : k → k := fun r => e'.symm (ρ (f r))
  have hi : Function.Bijective i :=
    e'.symm.bijective.comp (ρ.bijective.comp hf)
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv i
    (M := (ModuleCat.restrictScalars f).obj M) (M₁ := (ModuleCat.restrictScalars f').obj M')
    j hi fun r m => ?_)
  show j (f r • m) = f' (e'.symm (ρ (f r))) • j m
  exact (hj (f r) m).trans (congrArg (· • j m) (e'.apply_symm_apply (ρ (f r))).symm)

end SemilinearEquivalent

namespace SheafOfModules

open CategoryTheory

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- An isomorphism of sheaves of modules is a linear isomorphism of the modules of sections. -/
theorem semilinearEquivalent_of_iso {N N' : SheafOfModules.{u} R} (e : N ≅ N') (U : Cᵒᵖ) :
    SemilinearEquivalent (R.obj.obj U) (R.obj.obj U) (N.val.obj U) (N'.val.obj U) :=
  SemilinearEquivalent.of_linearEquiv ((SheafOfModules.evaluation R U).mapIso e).toLinearEquiv

/-- Restriction along an isomorphism of the site is semilinear along the restriction of
scalars. -/
theorem semilinearEquivalent_map (N : SheafOfModules.{u} R) {U U' : Cᵒᵖ} (a : U ≅ U') :
    SemilinearEquivalent (R.obj.obj U) (R.obj.obj U') (N.val.obj U) (N.val.obj U') :=
  ⟨(R.obj.mapIso a).ringCatIsoToRingEquiv,
    { toFun := N.val.map a.hom
      invFun := N.val.map a.inv
      left_inv := fun m => by
        have h2 : (N.val.map (a.hom ≫ a.inv)).hom m = m := by
          rw [a.hom_inv_id, N.val.map_id]; rfl
        rwa [N.val.map_comp] at h2
      right_inv := fun m => by
        have h2 : (N.val.map (a.inv ≫ a.hom)).hom m = m := by
          rw [a.inv_hom_id, N.val.map_id]; rfl
        rwa [N.val.map_comp] at h2
      map_add' := fun m m' => (N.val.map a.hom).hom.map_add m m' },
    fun r m => N.val.map_smul a.hom r m⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The morphism of a relocalized field-valued point is the extension of the morphism of the
point, read through the identification of `Λ_h Spec(k)` with `Spec(k)` over `S`. -/
theorem FieldValuedPoint.relocalize_toSpace {Y : AlgebraicSpaces B W hW}
    (p : FieldValuedPoint B W hW Y.1) :
    (FieldValuedPoint.relocalize B W S hW hS h Y.1 p).toSpace
        (Y := relocalizeSpaceSE B W S hW hS h Y) =
      (CoherentSituation.relocalizeSchemeSpaceIso h p.siteObject).inv ≫
        relocalizeHomSE B W S hW hS h p.toSpace := by
  apply ObjectProperty.hom_ext
  apply yonedaEquiv.injective
  rfl

/-- **The sections of the cohomology of `Ψ M` over a chart are those of the cohomology of `M` over
the extended chart.** -/
theorem semilinearEquivalent_homology_rebaseDerived (X : AlgebraicSpaces B W hW)
    (M : @DerivedCategory (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2) _ _
      (HasDerivedCategory.standard _)) (n : ℤ) (U : SmallEtale B W hW X.1) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW X.1 X.2)
    SemilinearEquivalent
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B W hW X.1 X.2).O).obj.obj
        (op U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS _ (relocalizeSpaceSE B W S hW hS h X).2).O).obj.obj
          (op ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.obj U)))
      (((DerivedCategory.homologyFunctor _ n).obj
        ((rebaseDerived B W S hW hS h X.2 (relocalizeSpaceSE B W S hW hS h X).2).obj M)).val.obj
          (op U))
      (((DerivedCategory.homologyFunctor _ n).obj M).val.obj
        (op ((SmallEtale.relocalizeEquivalence B W S hW hS h X.1).functor.obj U))) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
  let := HasDerivedCategory.standard (Modules.{u, u} B W hW X.1 X.2)
  refine (SheafOfModules.semilinearEquivalent_of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (rebaseRestriction B W S hW hS h X) n).app M) (op U)).trans ?_
  exact ⟨RingEquiv.refl _, AddEquiv.refl _, fun _ _ => rfl⟩

section Iso

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

variable {X X' : AlgebraicSpaces B S hS} (ι : X ≅ X')

/-- **Direct image of modules along an isomorphism of algebraic spaces is an equivalence**, with
quasi-inverse the direct image along the inverse isomorphism. -/
def modulePushforwardEquivalenceOfIso :
    Modules.{u, u} B S hS X.1 X.2 ≌ Modules.{u, u} B S hS X'.1 X'.2 :=
  CategoryTheory.Equivalence.mk (modulePushforward B S hS ι.hom) (modulePushforward B S hS ι.inv)
    ((modulePushforwardIdIso B S hS X).symm ≪≫
      eqToIso (congrArg (modulePushforward B S hS) ι.hom_inv_id.symm) ≪≫
      (modulePushforwardCompIso B S hS ι.hom ι.inv).symm)
    (modulePushforwardCompIso B S hS ι.inv ι.hom ≪≫
      eqToIso (congrArg (modulePushforward B S hS) ι.inv_hom_id) ≪≫
      modulePushforwardIdIso B S hS X')

/-- Direct image of modules along the inverse of an isomorphism of algebraic spaces is an
equivalence. -/
instance isEquivalence_modulePushforward_inv_of_algebraicSpacesIso :
    (modulePushforward B S hS ι.inv).IsEquivalence :=
  (modulePushforwardEquivalenceOfIso B S hS ι).symm.isEquivalence_functor

/-- **Derived pullback along an isomorphism is the direct image along the inverse, read on
derived categories**: `Lι^* ≅ (ι⁻¹)_*`. -/
def smallEtaleDerivedModulePullbackIsoMapDerivedOfIso :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    smallEtaleDerivedModulePullback B S hS ι.hom ≅
      (modulePushforward B S hS ι.inv).mapDerivedCategory :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  letI := isGrothendieckAbelian_modules B S hS X'.1 X'.2
  ((smallEtaleDerivedAdjunction B S hS ι.inv).rightAdjointUniq
      (smallEtaleDerivedModulePullbackEquivalenceOfIso ι.symm).toAdjunction).symm ≪≫
    smallEtaleDerivedModulePushforwardIso B S hS ι.inv ≪≫
    totalRightDerivedIsoMapDerivedCategoryOfExact _

/-- The underlying morphism of presheaves of the inverse of an isomorphism of algebraic spaces is
an isomorphism. -/
instance isIso_inv_hom_of_algebraicSpacesIso : IsIso ι.inv.hom :=
  inferInstanceAs (IsIso ((ObjectProperty.ι _).map ι.inv))

/-- The structure map of small-chart base change along an isomorphism is an isomorphism on every
chart. -/
theorem bijective_smallBaseChangeSharp_app_of_iso (c : SmallEtale B S hS X.1) :
    Function.Bijective ((smallBaseChangeSharp B S hS ι.inv
      (Functor.relativelyRepresentable.of_isIso yoneda ι.inv.hom)).hom.app (op c)) := by
  let hrep := Functor.relativelyRepresentable.of_isIso yoneda ι.inv.hom
  have hpb := hrep.isPullback c.1.hom
  have : IsIso (yoneda.map (hrep.snd c.1.hom)) := hpb.isIso_snd_of_isIso
  have : IsIso (hrep.snd c.1.hom) := isIso_of_fully_faithful yoneda _
  show Function.Bijective ((forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep.snd c.1.hom)).op))
  exact (ConcreteCategory.bijective_of_isIso _)

/-- **Sections of the cohomology of a derived pullback along an isomorphism**: over a chart `c` of
`X`, the cohomology of `Lι^*K` has the sections of the cohomology of `K` over the base change of
`c` along `ι⁻¹`, semilinearly along the pullback of functions. -/
theorem semilinearEquivalent_homology_pullback_of_iso
    (K : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) _ _
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))))
    (n : ℤ) (c : SmallEtale B S hS X.1) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
    SemilinearEquivalent ((ringedToposStructureRingSheaf B S hS X).obj.obj (op c))
      ((ringedToposStructureRingSheaf B S hS X').obj.obj (op ((smallBaseChange B S hS ι.inv
        (Functor.relativelyRepresentable.of_isIso yoneda ι.inv.hom)).obj c)))
      (((DerivedCategory.homologyFunctor _ n).obj
        ((smallEtaleDerivedModulePullback B S hS ι.hom).obj K)).val.obj (op c))
      (((DerivedCategory.homologyFunctor _ n).obj K).val.obj (op ((smallBaseChange B S hS ι.inv
        (Functor.relativelyRepresentable.of_isIso yoneda ι.inv.hom)).obj c))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  let hrep := Functor.relativelyRepresentable.of_isIso yoneda ι.inv.hom
  refine (SheafOfModules.semilinearEquivalent_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso
    ((smallEtaleDerivedModulePullbackIsoMapDerivedOfIso B S hS ι).app K)) (op c)).trans ?_
  refine (SheafOfModules.semilinearEquivalent_of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (modulePushforward B S hS ι.inv) n).app K) (op c)).trans ?_
  refine (SheafOfModules.semilinearEquivalent_of_iso
    ((modulePushforwardChartIso B S hS ι.inv hrep).app _) (op c)).trans ?_
  exact ⟨RingEquiv.ofBijective _ (bijective_smallBaseChangeSharp_app_of_iso B S hS ι c),
    AddEquiv.refl _, fun _ _ => rfl⟩

end Iso

section Betti

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

/-- The base change of the identity chart of `Spec(k)` over `S` along `Λ_h Spec(k) ≅ Spec(k)` is
the extension of the identity chart of `Spec(k)` over `W`. -/
def rebaseIdChartIso (V : BigFppfOver B W hW) :
    (smallBaseChange B S hS (CoherentSituation.relocalizeSchemeSpaceIso h V).symm.inv
      (Functor.relativelyRepresentable.of_isIso yoneda
        (CoherentSituation.relocalizeSchemeSpaceIso h V).symm.inv.hom)).obj
        (idChart B S hS ((Over.map h).obj V)) ≅
      (SmallEtale.relocalizeEquivalence B W S hW hS h (yoneda.obj V)).functor.obj
        (idChart B W hW V) := by
  let σ := CoherentSituation.relocalizeSchemeSpaceIso h V
  let hrep := Functor.relativelyRepresentable.of_isIso yoneda σ.symm.inv.hom
  have hpb := hrep.isPullback (idChart B S hS ((Over.map h).obj V)).1.hom
  haveI : IsIso (yoneda.map (hrep.snd (idChart B S hS ((Over.map h).obj V)).1.hom)) :=
    hpb.isIso_snd_of_isIso
  have hiso : IsIso (hrep.snd (idChart B S hS ((Over.map h).obj V)).1.hom) :=
    isIso_of_fully_faithful yoneda _
  refine ObjectProperty.isoMk _ (CostructuredArrow.isoMk
    (@asIso _ _ _ _ (hrep.snd (idChart B S hS ((Over.map h).obj V)).1.hom) hiso) ?_)
  have e1 : relocalizeChart B W S hW hS h (𝟙 (yoneda.obj V)) = σ.inv.hom := by
    rw [relocalizeChart, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have e2 : hrep.fst (idChart B S hS ((Over.map h).obj V)).1.hom ≫ σ.hom.hom =
      yoneda.map (hrep.snd (idChart B S hS ((Over.map h).obj V)).1.hom) :=
    hpb.w.trans (Category.comp_id _)
  have e3 : σ.hom.hom ≫ σ.inv.hom = 𝟙 _ := congrArg (fun f => f.hom) σ.hom_inv_id
  change yoneda.map (hrep.snd (idChart B S hS ((Over.map h).obj V)).1.hom) ≫
    relocalizeChart B W S hW hS h (𝟙 (yoneda.obj V)) = hrep.fst _
  rw [e1, ← e2]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e3).trans (Category.comp_id _))

/-- The map from the field of definition of a field-valued point to the sections of the structure
sheaf of `Spec(k)` over its identity chart is bijective. -/
theorem FieldValuedPoint.bijective_fieldToSections {T : Scheme.{u}} {hT : B.Contains T}
    {Z : AlgebraicSpaces B T hT} (q : FieldValuedPoint B T hT Z.1) :
    Function.Bijective q.fieldToSections.hom :=
  ConcreteCategory.bijective_of_isIso
    ((forget₂ CommRingCat RingCat).map (Scheme.ΓSpecIso (.of q.carrier)).inv)

/-- **The derived-fibre Betti numbers along the change of base scheme**: for an object `G` of
`D(𝒪_{Λ_h Y})` and a field-valued point `p` of `Y` over `W`, the Betti numbers of `Ψ G` at `p`
are those of `G` at `p` read over `S`. -/
theorem derivedFibreBettiAt_rebaseDerived (Y : AlgebraicSpaces B W hW)
    (G : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (relocalizeSpaceSE B W S hW hS h Y))) _ _ (HasDerivedCategory.standard
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (relocalizeSpaceSE B W S hW hS h Y)))))
    (n : ℤ) (p : FieldValuedPoint B W hW Y.1) :
    derivedFibreBettiAt Y
        ((rebaseDerived B W S hW hS h Y.2 (relocalizeSpaceSE B W S hW hS h Y).2).obj G) n p =
      derivedFibreBettiAt (relocalizeSpaceSE B W S hW hS h Y) G n
        (FieldValuedPoint.relocalize B W S hW hS h Y.1 p) := by
  let V := p.siteObject
  let φ : (schemeSpaceFunctor B W hW).obj V ⟶ Y := p.toSpace
  have hφ : yoneda.relativelyRepresentable φ.hom :=
    Functor.relativelyRepresentable.diag_iff.mp Y.2.diagonal_representable φ.hom
  let σ := CoherentSituation.relocalizeSchemeSpaceIso h V
  let M := (smallEtaleDerivedModulePullback B S hS (relocalizeHomSE B W S hW hS h φ)).obj G
  have a1 := SheafOfModules.semilinearEquivalent_of_iso
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).mapIso
      ((rebaseDerivedPullbackIso B W S hW hS h φ hφ).app G).symm) (op (idChart B W hW V))
  have a2 := semilinearEquivalent_homology_rebaseDerived B W S hW hS h
    ((schemeSpaceFunctor B W hW).obj V) M n (idChart B W hW V)
  have b1 := SheafOfModules.semilinearEquivalent_of_iso
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).mapIso
      ((smallEtaleDerivedModulePullbackCongr B S hS
        (FieldValuedPoint.relocalize_toSpace B W S hW hS h p)).app G ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS σ.inv
          (relocalizeHomSE B W S hW hS h φ)).app G).symm))
      (op (idChart B S hS ((Over.map h).obj V)))
  have b2 := semilinearEquivalent_homology_pullback_of_iso B S hS σ.symm M n
    (idChart B S hS ((Over.map h).obj V))
  have b3 := SheafOfModules.semilinearEquivalent_map
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).obj M)
    (rebaseIdChartIso B W S hW hS h V).op
  refine SemilinearEquivalent.finrank_restrictScalars_eq _ _
    (FieldValuedPoint.bijective_fieldToSections B (Z := Y) p)
    (FieldValuedPoint.bijective_fieldToSections B (Z := relocalizeSpaceSE B W S hW hS h Y)
      (FieldValuedPoint.relocalize B W S hW hS h Y.1 p)) ?_
  exact a1.trans (a2.trans (b3.trans (b2.symm.trans b1.symm)))

/-- **The derived-fibre Euler characteristic along the change of base scheme**: for a perfect
object `G` of `D(𝒪_{Λ_h Y})`, the Euler characteristic of `Ψ G` at a point `x` of `Y` is that of
`G` at the corresponding point of `Λ_h Y` (Stacks 03I5). -/
theorem derivedFibreEuler_rebaseDerived (Y : AlgebraicSpaces B W hW)
    (G : @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (relocalizeSpaceSE B W S hW hS h Y))) _ _ (HasDerivedCategory.standard
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
          (relocalizeSpaceSE B W S hW hS h Y)))))
    (hG : letI := HasDerivedCategory.standard
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2).O))
      (smallEtaleRingedSite B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2).IsPerfect G)
    (x : points B W hW Y.1) :
    derivedFibreEuler Y
        ((rebaseDerived B W S hW hS h Y.2 (relocalizeSpaceSE B W S hW hS h Y).2).obj G) x =
      derivedFibreEuler (relocalizeSpaceSE B W S hW hS h Y) G
        (pointsRelocalize B W S hW hS h Y.1 x) := by
  have hx : pointsRelocalize B W S hW hS h Y.1 x =
      (FieldValuedPoint.relocalize B W S hW hS h Y.1 (Quot.out x)).class B S hS _ := by
    conv_lhs => rw [← Quot.out_eq x]
    rfl
  rw [hx, derivedFibreEuler_class B S hS (relocalizeSpaceSE B W S hW hS h Y) G
    (derivedCategoryB_of_isPerfect B S hS _ G hG)]
  exact finsum_congr fun n => congrArg (fun b : ℕ => (n.negOnePow : ℤ) * (b : ℤ))
    (derivedFibreBettiAt_rebaseDerived B W S hW hS h Y G n (Quot.out x))

end Betti

end AlgebraicGeometry.Space

end
