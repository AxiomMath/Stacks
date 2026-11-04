module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseOverlap
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesQCohEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraphBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingKernelSections
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Stacks 0AF4, clause (1), over an affine base

In a formal glueing situation `(f : Y ⟶ X, Z, U, V)` whose ambient space `X` is represented by an
affine scheme, granted the two halves of Stacks 0AF0 (the unit and the counit of the adjunction
of Stacks 0AEY are invertible), every glueing triple `G = (U' ⟵ V' ⟶ Y')` with affine legs is
the restriction of an algebraic space affine over `X`.  The space is `Spec A` for the ring
`A = Γ(U') ×_{Γ(V')} Γ(Y')`, the ring of global sections of the module of Stacks 0AEX at the
module triple `(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})` of `G`.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.gluedFunctions`: the fibre product ring
  `Γ(U') ×_{Γ(V')} Γ(Y')`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.essSurj_affineGlueingFunctor_of_isAffine`:
  the essential surjectivity of clause (1) of Stacks 0AF4 over an affine base, from Stacks 0AF0.
* `AlgebraicGeometry.Space.FormalGlueingSituation.affineBaseEssSurj`: the same for every formal
  glueing situation over an affine base, unconditionally.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {E : Type u₁} [Category.{v₁} E] {A : Type u₂} [Category.{v₂} A]
    {Bb : Type u₃} [Category.{v₃} Bb] {T : Type u₄} [Category.{v₄} T]
    {F : E ⥤ A} {F' : A ⥤ E} {G : E ⥤ Bb} {G' : Bb ⥤ E}
    {L : A ⥤ T} {L' : T ⥤ A} {R : Bb ⥤ T} {R' : T ⥤ Bb} {N : E ⥤ T} {N' : T ⥤ E}

/-- The counit of the restricted adjunction of `toCommaPullbackAdjunctionRestrict` being
invertible at a glueing object, the transpose of the second projection is invertible. -/
theorem isIso_commaCounitRight_of_isIso_restrict_counit [HasPullbacks E]
    (adjF : F ⊣ F') (adjG : G ⊣ G')
    (adjL : L ⊣ L') (adjR : R ⊣ R') (adjN : N ⊣ N') (cF : F ⋙ L ≅ N) (cG : G ⋙ R ≅ N)
    {N'mid : T ⥤ E} (pFmid : L' ⋙ F' ≅ N'mid) (eN : N'mid ⟶ N') (pG : R' ⋙ G' ≅ N')
    (hpF : conjugateEquiv (adjF.comp adjL) adjN cF.inv = pFmid.hom ≫ eN)
    (hpG : conjugateEquiv (adjG.comp adjR) adjN cG.inv = pG.hom)
    (αIso : F ⋙ L ≅ G ⋙ R)
    (hα : ∀ M, αIso.hom.app M = cF.hom.app M ≫ cG.inv.app M)
    {r : Comma.fst L R ⋙ F' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    {s : Comma.snd L R ⋙ G' ⟶ (Comma.snd L R ⋙ R) ⋙ N'}
    (hr : r = Functor.whiskerRight (Functor.whiskerLeft (Comma.fst L R) adjL.unit) F' ≫
      Functor.whiskerLeft (Comma.fst L R ⋙ L) pFmid.hom ≫
      Functor.whiskerRight (Comma.natTrans L R) N'mid ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) eN)
    (hs : s = Functor.whiskerRight (Functor.whiskerLeft (Comma.snd L R) adjR.unit) G' ≫
      Functor.whiskerLeft (Comma.snd L R ⋙ R) pG.hom)
    {K : Comma L R ⥤ E} {κ₁ : K ⟶ Comma.fst L R ⋙ F'} {κ₂ : K ⟶ Comma.snd L R ⋙ G'}
    (hKnat : IsPullback κ₁ κ₂ r s)
    {E₀ : Type u₅} [Category.{v₅} E₀] {iE : E₀ ⥤ E} (ffE : iE.FullyFaithful)
    {Q : Type u₆} [Category.{v₆} Q] {iQ : Q ⥤ Comma L R} (ffQ : iQ.FullyFaithful)
    {Lq : E₀ ⥤ Q} {Rq : Q ⥤ E₀}
    (cq : (iE ⋙ F) ⋙ L ≅ (iE ⋙ G) ⋙ R) (hcq : cq = Functor.isoWhiskerLeft iE αIso)
    (comm₁ : Lq ⋙ iQ = Functor.toComma (iE ⋙ F) (iE ⋙ G) cq.hom)
    (comm₂ : iQ ⋙ K = Rq ⋙ iE) (adj : Lq ⊣ Rq)
    (hadj : adj = toCommaPullbackAdjunctionRestrict adjF adjG adjL adjR adjN cF cG pFmid eN pG
      hpF hpG αIso hα hr hs hKnat ffE ffQ cq hcq comm₁ comm₂)
    (t : Q) (X : Comma L R) (hX : iQ.obj t = X) (h : IsIso (adj.counit.app t)) :
    IsIso (commaCounitRight adjG κ₂ X) := by
  subst hX hadj
  have h1 : IsIso ((Comma.snd L R).map (iQ.map ((toCommaPullbackAdjunctionRestrict adjF adjG
      adjL adjR adjN cF cG pFmid eN pG hpF hpG αIso hα hr hs hKnat ffE ffQ cq hcq comm₁
      comm₂).counit.app t))) := inferInstance
  rw [toCommaPullbackAdjunctionRestrict, map_restrictFullyFaithful_counit_app,
    Functor.map_comp, Functor.map_comp] at h1
  have h3 := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h1
  have h2 := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance h3
  change IsIso ((adjG.homEquiv _ _).symm (𝟙 _ ≫ κ₂.app (iQ.obj t))) at h2
  rwa [Category.id_comp] at h2

end CategoryTheory.Adjunction

/-- A commutative square of modules commutes on elements. -/
theorem isPullback_moduleCat_apply {R : Type*} [Ring R] {K A B' C : ModuleCat.{u} R}
    {p₁ : K ⟶ A} {p₂ : K ⟶ B'} {ρ₁ : A ⟶ C} {ρ₂ : B' ⟶ C} (h : IsPullback p₁ p₂ ρ₁ ρ₂) (x : K) :
    ρ₁.hom (p₁.hom x) = ρ₂.hom (p₂.hom x) :=
  congrArg (fun q => q.hom x) h.w

/-- A pullback square of modules is a fibre product on elements: the two projections are jointly
injective, they commute with the two maps to the corner, and every compatible pair comes from
an element. -/
theorem isPullback_moduleCat_elements {R : Type*} [Ring R] {K A B' C : ModuleCat.{u} R}
    {p₁ : K ⟶ A} {p₂ : K ⟶ B'} {ρ₁ : A ⟶ C} {ρ₂ : B' ⟶ C} (h : IsPullback p₁ p₂ ρ₁ ρ₂) :
    (∀ x, ρ₁ (p₁ x) = ρ₂ (p₂ x)) ∧ (∀ x y, p₁ x = p₁ y → p₂ x = p₂ y → x = y) ∧
      (∀ a b, ρ₁ a = ρ₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) := by
  refine ⟨fun x => congrArg (fun q => q.hom x) h.w, fun x y h1 h2 =>
    (isPullbackFibreProductEquiv h).injective (Subtype.ext (Prod.ext h1 h2)), fun a b hab => ?_⟩
  obtain ⟨x, hx⟩ := (isPullbackFibreProductEquiv h).surjective
    ⟨(a, b), (mem_moduleFibreProduct_iff _).2 hab⟩
  exact ⟨x, congrArg (fun z => z.1.1) hx, congrArg (fun z => z.1.2) hx⟩

namespace AlgebraicGeometry.Space

/-- **One leg of the comparison is an isomorphism.**  If the pullback `q^*M` of a quasi-coherent
module is identified with `g_*𝒪_{Q'}` and `Γ(T)` with the global sections of `M`, compatibly
with `a : Q' ⟶ T`, then `Q' ⟶ Q ×_X T` is an isomorphism. -/
theorem isIso_pullbackLift_of_counit {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Q Q' : AlgebraicSpaces B S hS} (q : Q ⟶ X) (g : Q' ⟶ Q)
    (hg : IsAffineHom B S hS g.hom) (Z₀ : SmallEtale B S hS X.1) [IsIso Z₀.1.hom]
    [hZ : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)]
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (τ : T ⟶ (SmallEtale.toOver B S hS X.1).obj Z₀) (a : Q' ⟶ schemeSpace T)
    (ha : a.hom ≫ yoneda.map τ ≫ Z₀.1.hom = g.hom ≫ q.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (c : (modulePullback B S hS q).obj M ⟶
      (modulePushforward B S hS g).obj (SheafOfModules.unit (structureRingSheaf B S hS Q')))
    (hc : IsIso c)
    (φ : M ⟶ (modulePushforward B S hS q).obj
      ((modulePushforward B S hS g).obj (SheafOfModules.unit (structureRingSheaf B S hS Q'))))
    (hφ : (modulePullbackAdjunction B S hS q).homEquiv M _ c = φ)
    (hι : letI : Algebra (chartRing B S hS X.1 X.2 Z₀) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
      ∃ ι : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≃ₗ[chartRing B S hS X.1 X.2 Z₀]
          M.val.obj (op Z₀), ∀ t,
        pushforwardUnitGlobal B S hS (g ≫ q) Z₀
          ((φ ≫ (modulePushforwardCompIso B S hS g q).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS Q'))).val.app (op Z₀) (ι t)) =
          pullbackToGlobalFunctions B S hS Q' T a t) :
    IsIso (pullback.lift a.hom g.hom ha : Q'.1 ⟶ pullback (yoneda.map τ ≫ Z₀.1.hom) q.hom) := by
  let : Algebra (chartRing B S hS X.1 X.2 Z₀) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  obtain ⟨ι, hι⟩ := hι
  have := hc
  refine isIso_pullbackLift_of_bijective_tensor B S hS q g hg Z₀ τ a ha fun W hW => ?_
  let : Algebra (chartRing B S hS X.1 X.2 Z₀) (chartRing B S hS Q.1 Q.2 W) :=
    chartDiagramAlgebra B S hS q (isoChartDiagram B S hS q Z₀ W)
  obtain ⟨e', he'⟩ := exists_tensorChartEquiv B S hS q g
    (relativelyRepresentable_of_isAffineHom B S hS g hg) Z₀ M hM
    c W hW hZ
  refine ⟨(LinearEquiv.lTensor (chartRing B S hS Q.1 Q.2 W) ι).toAddEquiv.trans e',
    fun w t => ?_⟩
  refine (he' w (ι t)).trans ?_
  refine congrArg₂ (fun x y => x * y) rfl ?_
  rw [← hι t, ← hφ]
  exact (pushforwardUnitGlobal_comp_compIso_apply B S hS g q Z₀ _ _ _
    (isoChartDiagram B S hS q Z₀ _).g _ (isoChartDiagram B S hS q Z₀ _).comm).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS) (G : (affineLegs D).FullSubcategory)

/-- The fibre product ring `Γ(U') ×_{Γ(V')} Γ(Y')` of a glueing triple. -/
def gluedFunctions :
    Subring (globalFunctions B S hS (D.affLegU G).1 × globalFunctions B S hS (D.affLegY G).1) :=
  RingHom.eqLocus ((globalFunctionsMap B S hS (D.affLegVU G)).comp (RingHom.fst _ _))
    ((globalFunctionsMap B S hS (D.affLegVY G)).comp (RingHom.snd _ _))

/-- Membership in the fibre product ring. -/
theorem mem_gluedFunctions (p : globalFunctions B S hS (D.affLegU G).1 ×
    globalFunctions B S hS (D.affLegY G).1) :
    p ∈ D.gluedFunctions G ↔
      globalFunctionsMap B S hS (D.affLegVU G) p.1 = globalFunctionsMap B S hS (D.affLegVY G) p.2 :=
  Iff.rfl

/-- The fibre product ring is `u`-small. -/
instance : Small.{u} (D.gluedFunctions G) := inferInstance

/-- The fibre product ring, as a ring in the universe of the schemes. -/
abbrev gluedRing : Type u := Shrink.{u} (D.gluedFunctions G)

/-- The spectrum of the fibre product ring lies in the site. -/
theorem contains_spec_gluedRing : B.Contains (Spec (CommRingCat.of (D.gluedRing G))) := by
  let DU := chosenAtlasKernelPair B S hS (D.affLegU G)
  let DY := chosenAtlasKernelPair B S hS (D.affLegY G)
  let VU := (BigFppfOver.toScheme B S hS).obj DU.U
  let VY := (BigFppfOver.toScheme B S hS).obj DY.U
  let ι : D.gluedRing G → Γ(VU, ⊤) × Γ(VY, ⊤) := fun a =>
    (globalFunctionsChartRestriction B S hS (D.affLegU G)
        (chartFromEtaleHom B S hS _ DU.U DU.f DU.etale)
        ((equivShrink (D.gluedFunctions G)).symm a).1.1,
      globalFunctionsChartRestriction B S hS (D.affLegY G)
        (chartFromEtaleHom B S hS _ DY.U DY.f DY.etale)
        ((equivShrink (D.gluedFunctions G)).symm a).1.2)
  have hι : Function.Injective ι := fun a b hab =>
    (equivShrink (D.gluedFunctions G)).symm.injective (Subtype.ext (Prod.ext
      (globalFunctionsChartRestriction_injective B S hS _ DU (congrArg Prod.fst hab))
      (globalFunctionsChartRestriction_injective B S hS _ DY (congrArg Prod.snd hab))))
  have hU : Cardinal.mk Γ(VU, ⊤) < B.cutoff :=
    lt_of_le_of_lt (VU.mk_sections_le_two_pow_size ⊤)
      (B.cutoff_isStrongPrelimit DU.U.left.property)
  have hY : Cardinal.mk Γ(VY, ⊤) < B.cutoff :=
    lt_of_le_of_lt (VY.mk_sections_le_two_pow_size ⊤)
      (B.cutoff_isStrongPrelimit DY.U.left.property)
  show (Spec (CommRingCat.of (D.gluedRing G))).size < B.cutoff
  rw [Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt (Cardinal.mk_le_of_injective hι) ?_)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt (le_of_lt B.aleph0_lt_cutoff) hU hY

omit G in
/-- On sections over `Z₀`, the two projections of the glueing kernel agree after the maps to the
overlap. -/
theorem kernel_overlap (Z₀ : SmallEtale B S hS D.spaceX.1) (t : D.moduleGlueingComma)
    (k : (D.sectionsAt t Z₀).obj D.glueingKernelDiagram) :
    ((D.sectionsAt t Z₀).map D.restrictionOverlapMap).hom
        (((D.sectionsAt t Z₀).map D.glueingKernelFst).hom k) =
      ((D.sectionsAt t Z₀).map D.ambientOverlapMap).hom
        (((D.sectionsAt t Z₀).map D.glueingKernelSnd).hom k) :=
  isPullback_moduleCat_apply (D.isPullback_glueingKernel_sections t Z₀) k

variable (Z₀ : SmallEtale B S hS D.spaceX.1) [hZ₀ : IsIso Z₀.1.hom]
    [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)]

/-- The leg `U' ⟶ Z₀`. -/
def affLegUToBase : D.affLegU G ⟶ schemeSpace ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀) :=
  ObjectProperty.homMk ((D.affLegUHom G).hom ≫ D.openImmersion.hom ≫ (asIso Z₀.1.hom).inv)

/-- The leg `Y' ⟶ Z₀`. -/
def affLegYToBase : D.affLegY G ⟶ schemeSpace ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀) :=
  ObjectProperty.homMk ((D.affLegYHom G).hom ≫ D.ambientMorphism.hom ≫ (asIso Z₀.1.hom).inv)

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The two legs `V' ⟶ U' ⟶ Z₀` and `V' ⟶ Y' ⟶ Z₀` agree. -/
theorem affLegVU_comp_affLegUToBase :
    D.affLegVU G ≫ D.affLegUToBase G Z₀ = D.affLegVY G ≫ D.affLegYToBase G Z₀ := by
  apply ObjectProperty.hom_ext
  show (D.affLegVU G).hom ≫ (D.affLegUHom G).hom ≫ D.openImmersion.hom ≫ (asIso Z₀.1.hom).inv =
    (D.affLegVY G).hom ≫ (D.affLegYHom G).hom ≫ D.ambientMorphism.hom ≫ (asIso Z₀.1.hom).inv
  have h1 := congrArg (fun k => k.hom) (D.isPullback_affLegVU G).w
  have h2 := congrArg (fun k => k.hom) (D.isPullback_affLegVY G).w
  have h3 := congrArg (fun k => k.hom) D.overlapRestriction_comp_openImmersion
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h1 h2 h3
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc D.overlapRestriction.hom, h3,
    Category.assoc, ← Category.assoc (D.affLegVY G).hom, h2, Category.assoc]

/-- The structure map `Γ(Z₀) ⟶ Γ(U') ×_{Γ(V')} Γ(Y')`. -/
def gluedFunctionsAlgebraMap :
    Γ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀, ⊤) →+*
      D.gluedFunctions G :=
  ((pullbackToGlobalFunctions B S hS (D.affLegU G) _ (D.affLegUToBase G Z₀)).prod
    (pullbackToGlobalFunctions B S hS (D.affLegY G) _ (D.affLegYToBase G Z₀))).codRestrict _
    fun r => by
      rw [mem_gluedFunctions]
      change ((globalFunctionsMap B S hS (D.affLegVU G)).comp
          (pullbackToGlobalFunctions B S hS (D.affLegU G) _ (D.affLegUToBase G Z₀))) r =
        ((globalFunctionsMap B S hS (D.affLegVY G)).comp
          (pullbackToGlobalFunctions B S hS (D.affLegY G) _ (D.affLegYToBase G Z₀))) r
      rw [← pullbackToGlobalFunctions_comp_left, ← pullbackToGlobalFunctions_comp_left,
        affLegVU_comp_affLegUToBase]

/-- The structure map `Γ(Z₀) ⟶ A`. -/
def gluedRingAlgebraMap :
    Γ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀, ⊤) →+*
      D.gluedRing G :=
  (Shrink.ringEquiv (D.gluedFunctions G)).symm.toRingHom.comp (D.gluedFunctionsAlgebraMap G Z₀)

/-- The morphism of schemes `Spec A ⟶ Z₀`. -/
def gluedSpecToBase : Spec (CommRingCat.of (D.gluedRing G)) ⟶
    (SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀ :=
  Spec.map (CommRingCat.ofHom (D.gluedRingAlgebraMap G Z₀)) ≫
    ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀).isoSpec.inv

/-- **The glued space** `Spec A`, as an object of the site. -/
def gluedObject : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (D.contains_spec_gluedRing G)
    (D.gluedSpecToBase G Z₀ ≫ B.inclusion.map ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀).hom)

/-- The scheme `Spec A` underlying the glued object is affine. -/
instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (D.gluedRing G))))

/-- The structure morphism `Spec A ⟶ Z₀` in the site. -/
def gluedObjectHom : D.gluedObject G Z₀ ⟶ (SmallEtale.toOver B S hS D.spaceX.1).obj Z₀ :=
  Over.homMk (ObjectProperty.homMk (D.gluedSpecToBase G Z₀)) rfl

/-- The ring map `Γ(Spec A) ⟶ Γ(U')`. -/
def gluedRingToLegU : Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) →+*
    globalFunctions B S hS (D.affLegU G).1 :=
  (RingHom.fst _ _).comp ((D.gluedFunctions G).subtype.comp
    ((Shrink.ringEquiv (D.gluedFunctions G)).toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom))

/-- The ring map `Γ(Spec A) ⟶ Γ(Y')`. -/
def gluedRingToLegY : Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) →+*
    globalFunctions B S hS (D.affLegY G).1 :=
  (RingHom.snd _ _).comp ((D.gluedFunctions G).subtype.comp
    ((Shrink.ringEquiv (D.gluedFunctions G)).toRingHom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom))

/-- On global functions, `Spec A ⟶ Z₀` is the structure map of `A`, read through
`Γ(Spec A) ≅ A`. -/
theorem gluedObjectHom_appTop (r) :
    (Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom r) =
      D.gluedRingAlgebraMap G Z₀ r := by
  let Zs := (SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀
  have h1 : Zs.toSpecΓ.appTop ≫ Zs.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ, Scheme.Hom.id_appTop]
  rw [Scheme.toSpecΓ_appTop] at h1
  have h2 : Zs.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Zs, ⊤)).hom = 𝟙 _ := by
    have h3 : Zs.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Zs, ⊤)).inv := by
      rw [← Category.id_comp Zs.isoSpec.inv.appTop, ← Iso.inv_hom_id (Scheme.ΓSpecIso Γ(Zs, ⊤)),
        Category.assoc, h1, Category.comp_id]
    rw [h3, Iso.inv_hom_id]
  have key : ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom =
      CommRingCat.ofHom (D.gluedRingAlgebraMap G Z₀) := by
    show (Spec.map (CommRingCat.ofHom (D.gluedRingAlgebraMap G Z₀)) ≫
      Zs.isoSpec.inv).appTop ≫ _ = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc]
    exact (congrArg (· ≫ CommRingCat.ofHom (D.gluedRingAlgebraMap G Z₀)) h2).trans
      (Category.id_comp _)
  exact congrArg (fun k => k.hom r) key

/-- The scheme underlying `Z₀` in the big site is affine. -/
instance isAffine_toOver_obj_Z₀ :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀)) :=
  inferInstanceAs
    (IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))

/-- The composite `Γ(Z₀) ⟶ Γ(Spec A) ⟶ Γ(U')` is the map on global functions of `U' ⟶ Z₀`. -/
theorem gluedRingToLegU_comp :
    (D.gluedRingToLegU G Z₀).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom =
      pullbackToGlobalFunctions B S hS (D.affLegU G) _ (D.affLegUToBase G Z₀) := by
  refine RingHom.ext fun r => ?_
  show ((Shrink.ringEquiv (D.gluedFunctions G))
    ((Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom
        r))).1.1 = _
  rw [gluedObjectHom_appTop]
  show ((Shrink.ringEquiv (D.gluedFunctions G)) ((Shrink.ringEquiv (D.gluedFunctions G)).symm
    (D.gluedFunctionsAlgebraMap G Z₀ r))).1.1 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The composite `Γ(Z₀) ⟶ Γ(Spec A) ⟶ Γ(Y')` is the map on global functions of `Y' ⟶ Z₀`. -/
theorem gluedRingToLegY_comp :
    (D.gluedRingToLegY G Z₀).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom =
      pullbackToGlobalFunctions B S hS (D.affLegY G) _ (D.affLegYToBase G Z₀) := by
  refine RingHom.ext fun r => ?_
  show ((Shrink.ringEquiv (D.gluedFunctions G))
    ((Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom
        r))).1.2 = _
  rw [gluedObjectHom_appTop]
  show ((Shrink.ringEquiv (D.gluedFunctions G)) ((Shrink.ringEquiv (D.gluedFunctions G)).symm
    (D.gluedFunctionsAlgebraMap G Z₀ r))).1.2 = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The morphism `U' ⟶ Spec A` over `Z₀`, by Stacks 05Z1 in its relative form. -/
def gluedMapU : {m : D.affLegU G ⟶ schemeSpace (D.gluedObject G Z₀) //
    m ≫ schemeSpaceMap (D.gluedObjectHom G Z₀) = D.affLegUToBase G Z₀} :=
  (morphismToAffineOverEquiv B S hS (D.affLegU G) (D.gluedObjectHom G Z₀)
    (D.affLegUToBase G Z₀)).1.symm ⟨D.gluedRingToLegU G Z₀, D.gluedRingToLegU_comp G Z₀⟩

/-- The morphism `Y' ⟶ Spec A` over `Z₀`, by Stacks 05Z1 in its relative form. -/
def gluedMapY : {m : D.affLegY G ⟶ schemeSpace (D.gluedObject G Z₀) //
    m ≫ schemeSpaceMap (D.gluedObjectHom G Z₀) = D.affLegYToBase G Z₀} :=
  (morphismToAffineOverEquiv B S hS (D.affLegY G) (D.gluedObjectHom G Z₀)
    (D.affLegYToBase G Z₀)).1.symm ⟨D.gluedRingToLegY G Z₀, D.gluedRingToLegY_comp G Z₀⟩

/-- On global functions, `U' ⟶ Spec A` is the projection `Γ(Spec A) ⟶ Γ(U')`. -/
theorem pullbackToGlobalFunctions_gluedMapU :
    pullbackToGlobalFunctions B S hS (D.affLegU G) _ (D.gluedMapU G Z₀).1 =
      D.gluedRingToLegU G Z₀ := by
  have h := (morphismToAffineOverEquiv B S hS (D.affLegU G) (D.gluedObjectHom G Z₀)
    (D.affLegUToBase G Z₀)).2 (D.gluedMapU G Z₀)
  rw [← h]
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- On global functions, `Y' ⟶ Spec A` is the projection `Γ(Spec A) ⟶ Γ(Y')`. -/
theorem pullbackToGlobalFunctions_gluedMapY :
    pullbackToGlobalFunctions B S hS (D.affLegY G) _ (D.gluedMapY G Z₀).1 =
      D.gluedRingToLegY G Z₀ := by
  have h := (morphismToAffineOverEquiv B S hS (D.affLegY G) (D.gluedObjectHom G Z₀)
    (D.affLegYToBase G Z₀)).2 (D.gluedMapY G Z₀)
  rw [← h]
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The two maps agree on the overlap `V'`. -/
theorem affLegVU_comp_gluedMapU :
    D.affLegVU G ≫ (D.gluedMapU G Z₀).1 = D.affLegVY G ≫ (D.gluedMapY G Z₀).1 := by
  apply pullbackToGlobalFunctions_injective B S hS (D.affLegV G) (D.gluedObject G Z₀)
  rw [pullbackToGlobalFunctions_comp_left, pullbackToGlobalFunctions_comp_left,
    pullbackToGlobalFunctions_gluedMapU, pullbackToGlobalFunctions_gluedMapY]
  refine RingHom.ext fun r => ?_
  exact ((Shrink.ringEquiv (D.gluedFunctions G))
    ((Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom r)).2

include hZ₀ in
/-- **The glued space over `X`**: `Spec A ⟶ Z₀ ≅ X`. -/
def gluedSpace : (affineOverX D).FullSubcategory :=
  ⟨⟨Over.mk (yoneda.map (D.gluedObjectHom G Z₀) ≫ Z₀.1.hom),
    isAlgebraicSpace_yoneda B S hS _⟩,
    isAffineHom_comp B S hS _ _ (isAffineHom_yoneda_map B S hS _)
      (@isAffineHom_of_isIso B S hS _ _ Z₀.1.hom hZ₀)⟩

/-- The underlying morphism of presheaves of `U' ⟶ Spec A`. -/
def gluedMapUHom : G.obj.obj.left.left ⟶ yoneda.obj (D.gluedObject G Z₀) :=
  (D.gluedMapU G Z₀).1.hom

/-- The underlying morphism of presheaves of `Y' ⟶ Spec A`. -/
def gluedMapYHom : G.obj.obj.right.left ⟶ yoneda.obj (D.gluedObject G Z₀) :=
  (D.gluedMapY G Z₀).1.hom

/-- The composite `U' ⟶ Spec A ⟶ Z₀ ≅ X` is the structure map `U' ⟶ U ⟶ X`. -/
theorem gluedMapU_hom_comp :
    D.gluedMapUHom G Z₀ ≫ yoneda.map (D.gluedObjectHom G Z₀) ≫ Z₀.1.hom =
      (G.obj.obj.left.hom ≫ D.U.ι) := by
  have h : ((D.gluedMapU G Z₀).1 ≫ schemeSpaceMap (D.gluedObjectHom G Z₀)).hom ≫ Z₀.1.hom =
      (D.affLegUToBase G Z₀).hom ≫ Z₀.1.hom := by rw [(D.gluedMapU G Z₀).2]
  refine (Category.assoc _ _ _).symm.trans (h.trans ?_)
  show ((D.affLegUHom G).hom ≫ D.openImmersion.hom ≫ (asIso Z₀.1.hom).inv) ≫ Z₀.1.hom = _
  simp only [Category.assoc, Category.comp_id, asIso_inv, IsIso.inv_hom_id]
  rfl

/-- The composite `Y' ⟶ Spec A ⟶ Z₀ ≅ X` is the structure map `Y' ⟶ Y ⟶ X`. -/
theorem gluedMapY_hom_comp :
    D.gluedMapYHom G Z₀ ≫ yoneda.map (D.gluedObjectHom G Z₀) ≫ Z₀.1.hom =
      (G.obj.obj.right.hom ≫ D.f) := by
  have h : ((D.gluedMapY G Z₀).1 ≫ schemeSpaceMap (D.gluedObjectHom G Z₀)).hom ≫ Z₀.1.hom =
      (D.affLegYToBase G Z₀).hom ≫ Z₀.1.hom := by rw [(D.gluedMapY G Z₀).2]
  refine (Category.assoc _ _ _).symm.trans (h.trans ?_)
  show ((D.affLegYHom G).hom ≫ D.ambientMorphism.hom ≫ (asIso Z₀.1.hom).inv) ≫ Z₀.1.hom = _
  simp only [Category.assoc, Category.comp_id, asIso_inv, IsIso.inv_hom_id]
  rfl

/-- The `U`-component `U' ⟶ U ×_X Spec A` of the comparison. -/
def gluedLeft : G.obj.obj.left ⟶ (Over.pullback D.U.ι).obj (D.gluedSpace G Z₀).obj.obj :=
  Over.homMk (pullback.lift (D.gluedMapUHom G Z₀) G.obj.obj.left.hom
    (D.gluedMapU_hom_comp G Z₀)) (pullback.lift_snd _ _ _)

/-- The `Y`-component `Y' ⟶ Y ×_X Spec A` of the comparison. -/
def gluedRight : G.obj.obj.right ⟶ (Over.pullback D.f).obj (D.gluedSpace G Z₀).obj.obj :=
  Over.homMk (pullback.lift (D.gluedMapYHom G Z₀) G.obj.obj.right.hom
    (D.gluedMapY_hom_comp G Z₀)) (pullback.lift_snd _ _ _)

/-- The comparison is compatible with the structure isomorphisms over `V`. -/
theorem gluedLeft_w :
    (Over.pullback (D.U.fromPreimage D.f)).map (D.gluedLeft G Z₀) ≫
        (restrictionComparison D).hom.app (D.gluedSpace G Z₀).obj.obj =
      G.obj.obj.hom ≫ (Over.pullback D.V.ι).map (D.gluedRight G Z₀) := by
  have hV := congrArg (fun k => k.hom) (D.affLegVU_comp_gluedMapU G Z₀)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hV
  change pullback.fst _ _ ≫ D.gluedMapUHom G Z₀ =
    (G.obj.obj.hom.left ≫ pullback.fst _ _) ≫ D.gluedMapYHom G Z₀ at hV
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      refine (congrArg (_ ≫ ·)
        (D.restrictionComparison_hom_app_left_fst_fst (D.gluedSpace G Z₀).obj.obj)).trans ?_
      simp only [Over.pullback_map_left, gluedLeft, gluedRight, Over.homMk_left,
        pullback.lift_fst_assoc, Category.assoc]
      refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
      refine (congrArg (fun k => pullback.fst G.obj.obj.left.hom (D.U.fromPreimage D.f) ≫ k)
        (pullback.lift_fst _ _ _)).trans ?_
      refine Eq.trans ?_ (congrArg (fun k => G.obj.obj.hom.left ≫
        pullback.fst G.obj.obj.right.hom D.V.ι ≫ k) (pullback.lift_fst _ _ _)).symm
      exact hV.trans (Category.assoc _ _ _)
    · have h3 := (Over.w ((Over.pullback (D.U.fromPreimage D.f)).map (D.gluedLeft G Z₀) ≫
          (restrictionComparison D).hom.app (D.gluedSpace G Z₀).obj.obj)).trans
        (Over.w (G.obj.obj.hom ≫ (Over.pullback D.V.ι).map (D.gluedRight G Z₀))).symm
      simp only [Category.assoc]
      refine (congrArg (_ ≫ ·) pullback.condition).trans ?_
      refine Eq.trans ?_ (congrArg (_ ≫ ·) pullback.condition).symm
      simp only [← Category.assoc]
      exact congrArg (· ≫ D.V.ι) h3
  · exact (Over.w ((Over.pullback (D.U.fromPreimage D.f)).map (D.gluedLeft G Z₀) ≫
          (restrictionComparison D).hom.app (D.gluedSpace G Z₀).obj.obj)).trans
        (Over.w (G.obj.obj.hom ≫ (Over.pullback D.V.ι).map (D.gluedRight G Z₀))).symm

/-- The comparison morphism `G ⟶ F(Spec A)` of glueing triples. -/
def gluedComparison : G.obj.obj ⟶ ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀)).obj.obj :=
  ⟨D.gluedLeft G Z₀, D.gluedRight G Z₀, D.gluedLeft_w G Z₀⟩

/-- **Essential surjectivity at one triple, from the two comparison legs.** -/
theorem nonempty_iso_of_isIso_gluedLeft_gluedRight
    (hL : IsIso (D.gluedLeft G Z₀).left) (hR : IsIso (D.gluedRight G Z₀).left) :
    Nonempty ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀) ≅ G) := by
  have : IsIso ((Over.forget _).map (D.gluedLeft G Z₀)) := hL
  have : IsIso ((Over.forget _).map (D.gluedRight G Z₀)) := hR
  have : IsIso (D.gluedLeft G Z₀) := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso (D.gluedRight G Z₀) := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso (D.gluedComparison G Z₀).left := inferInstanceAs (IsIso (D.gluedLeft G Z₀))
  have : IsIso (D.gluedComparison G Z₀).right := inferInstanceAs (IsIso (D.gluedRight G Z₀))
  have : IsIso (D.gluedComparison G Z₀) :=
    Comma.isIso_of_isIso_left_right (D.gluedComparison G Z₀)
  let e : G.obj.obj ≅ ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀)).obj.obj :=
    asIso (D.gluedComparison G Z₀)
  let e' : G.obj ≅ ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀)).obj :=
    ((show ObjectProperty (Comma (Over.pullback (D.U.fromPreimage D.f)) (Over.pullback D.V.ι))
      from fun T ↦ IsIso T.hom ∧ IsAlgebraicSpace B S hS T.left.left ∧
        IsAlgebraicSpace B S hS T.right.left).fullyFaithfulι).preimageIso e
  exact ⟨((affineLegs D).fullyFaithfulι.preimageIso
    (X := (affineGlueingFunctor D).obj (D.gluedSpace G Z₀)) (Y := G) e'.symm)⟩

/-! ### The global sections of the module of Stacks 0AEX -/

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The leg `U' ⟶ Z₀` is `U' ⟶ X` followed by the inverse of `Z₀ ≅ X`. -/
theorem affLegUToBase_eq : D.affLegUToBase G Z₀ =
    ObjectProperty.homMk ((D.affLegUHom G ≫ D.openImmersion).hom ≫ (asIso Z₀.1.hom).inv) :=
  ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The leg `Y' ⟶ Z₀` is `Y' ⟶ X` followed by the inverse of `Z₀ ≅ X`. -/
theorem affLegYToBase_eq : D.affLegYToBase G Z₀ =
    ObjectProperty.homMk ((D.affLegYHom G ≫ D.ambientMorphism).hom ≫ (asIso Z₀.1.hom).inv) :=
  ObjectProperty.hom_ext _ (Category.assoc _ _ _).symm

omit G in
/-- The counit of Stacks 0AEY being invertible, its right component `β` is invertible. -/
theorem isIso_glueingCounitRight_of_isIso_counit (hcounit : IsIso D.glueingAdjunction.counit)
    (t : D.moduleGlueingData) : IsIso (D.glueingCounitRight t) :=
  Adjunction.isIso_commaCounitRight_of_isIso_restrict_counit
    (E₀ := QuasicoherentSheaves.{u, u} B S hS D.spaceX.1 D.spaceX.2) (Q := D.moduleGlueingData)
    (Lq := D.glueingModulesFunctor) (Rq := D.glueingKernelFunctor)
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.openImmersionOver)
    (modulePullbackAdjunction B S hS (D.openImmersionOver ≫ D.ambientMorphism))
    D.overlapPullbackCompIso
    (modulePullbackCompIso B S hS D.openImmersionOver D.ambientMorphism)
    (modulePushforwardCompIso B S hS D.overlapRestriction D.openImmersion)
    (eqToHom (congrArg (fun g : D.spaceV ⟶ D.spaceX => modulePushforward B S hS g)
      D.overlapRestriction_comp_openImmersion))
    (modulePushforwardCompIso B S hS D.openImmersionOver D.ambientMorphism)
    D.conjugateEquiv_overlapPullbackCompIso_inv
    D.conjugateEquiv_modulePullbackCompIso_overlap_inv
    D.overlapPullbackComparison D.overlapPullbackComparison_hom_app
    D.restrictionOverlapMap_eq D.ambientOverlapMap_eq D.isPullback_glueingKernel
    (show D.ambientInclusion.FullyFaithful from ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)
    D.quasicoherentOverlapComparison D.quasicoherentOverlapComparison_eq rfl rfl
    D.glueingAdjunction D.glueingAdjunction_eq t t.obj rfl
    (NatIso.isIso_app_of_isIso _ t)

omit G in
/-- The adjoint transpose of the left counit component is the first kernel projection. -/
theorem homEquiv_glueingCounitLeft (t : D.moduleGlueingData) :
    (modulePullbackAdjunction B S hS D.openImmersion).homEquiv (D.glueingKernelDiagram.obj t.obj)
        t.obj.left (D.glueingCounitLeft t) = D.glueingKernelFst.app t.obj :=
  Equiv.apply_symm_apply _ _

omit G in
/-- The adjoint transpose of the right counit component is the second kernel projection. -/
theorem homEquiv_glueingCounitRight (t : D.moduleGlueingData) :
    (modulePullbackAdjunction B S hS D.ambientMorphism).homEquiv (D.glueingKernelDiagram.obj t.obj)
        t.obj.right (D.glueingCounitRight t) = D.glueingKernelSnd.app t.obj :=
  Equiv.apply_symm_apply _ _

/-- The ring isomorphism `Γ(Spec A) ≅ Γ(U') ×_{Γ(V')} Γ(Y')`. -/
def gluedObjectGamma : Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) ≃+*
    D.gluedFunctions G :=
  (Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).commRingCatIsoToRingEquiv.trans
    (Shrink.ringEquiv (D.gluedFunctions G))

/-- Under `Γ(Spec A) ≅ Γ(U') ×_{Γ(V')} Γ(Y')`, the map from `Γ(Z₀)` is the structure map of the
fibre product ring. -/
theorem gluedObjectGamma_algebraMap (r) :
    D.gluedObjectGamma G Z₀
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom r) =
      D.gluedFunctionsAlgebraMap G Z₀ r := by
  show Shrink.ringEquiv _ ((Scheme.ΓSpecIso (CommRingCat.of (D.gluedRing G))).hom.hom _) = _
  rw [gluedObjectHom_appTop]
  exact RingEquiv.apply_symm_apply _ _

/-! ### Assembly -/

omit G Z₀ hZ₀
  [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- **Fibre products of types, read through bijections.**  If `P` is the fibre product of `r₁` and
`r₂` with projections `p₁`, `p₂`, and the three corners are read bijectively (injectively on the
base) as `Γ₁`, `Γ₂`, `Γ₃` compatibly with `ρ₁ : Γ₁ ⟶ Γ₃` and `ρ₂ : Γ₂ ⟶ Γ₃`, then `P` is the fibre
product of `ρ₁` and `ρ₂`. -/
theorem fibreProduct_of_readings {P A₁ A₂ C Γ₁ Γ₂ Γ₃ : Type*} (p₁ : P → A₁) (p₂ : P → A₂)
    (r₁ : A₁ → C) (r₂ : A₂ → C) (hw : ∀ x, r₁ (p₁ x) = r₂ (p₂ x))
    (hinj : ∀ x y, p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ a b, r₁ a = r₂ b → ∃ x, p₁ x = a ∧ p₂ x = b)
    (R₁ : A₁ → Γ₁) (R₂ : A₂ → Γ₂) (R₃ : C → Γ₃) (hR₁ : Function.Bijective R₁)
    (hR₂ : Function.Bijective R₂) (hR₃ : Function.Injective R₃) (ρ₁ : Γ₁ → Γ₃) (ρ₂ : Γ₂ → Γ₃)
    (h₁ : ∀ a, R₃ (r₁ a) = ρ₁ (R₁ a)) (h₂ : ∀ b, R₃ (r₂ b) = ρ₂ (R₂ b)) :
    (∀ x, ρ₁ (R₁ (p₁ x)) = ρ₂ (R₂ (p₂ x))) ∧
      (∀ x y, R₁ (p₁ x) = R₁ (p₁ y) → R₂ (p₂ x) = R₂ (p₂ y) → x = y) ∧
      (∀ γ₁ γ₂, ρ₁ γ₁ = ρ₂ γ₂ → ∃ x, R₁ (p₁ x) = γ₁ ∧ R₂ (p₂ x) = γ₂) := by
  refine ⟨fun x => ?_, fun x y h1 h2 => hinj x y (hR₁.1 h1) (hR₂.1 h2), fun γ₁ γ₂ h => ?_⟩
  · rw [← h₁, ← h₂, hw]
  · obtain ⟨a, rfl⟩ := hR₁.2 γ₁
    obtain ⟨b, rfl⟩ := hR₂.2 γ₂
    obtain ⟨x, hx1, hx2⟩ := hsurj a b (hR₃ ((h₁ a).trans (h.trans (h₂ b).symm)))
    exact ⟨x, by rw [hx1], by rw [hx2]⟩

section Triple

variable (t : D.moduleGlueingComma)
    (eL : (Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t ≅
      (modulePushforward B S hS (D.affLegUHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))
    (eR : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t ≅
      (modulePushforward B S hS (D.affLegYHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))
    (γ : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver) ⋙
        modulePullback B S hS D.openImmersionOver).obj t ⟶
      (modulePushforward B S hS (D.affLegVHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G))))
    (hγY : γ = (modulePullback B S hS D.openImmersionOver).map eR.hom ≫
      (modulePullbackPushforwardUnitIso (D.isPullback_affLegVY G) G.property.2.2).hom)
    (hγU : (Comma.natTrans (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).app t ≫ γ =
      (modulePullback B S hS D.overlapRestriction).map eL.hom ≫
        (modulePullbackPushforwardUnitIso (D.isPullback_affLegVU G) G.property.1).hom)

omit hZ₀
  [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The sections over `Z₀` of the glueing kernel square at `t` form a pullback square. -/
theorem sections_isPullback_glueingKernel :
    IsPullback ((D.glueingKernelFst.app t).val.app (op Z₀))
      ((D.glueingKernelSnd.app t).val.app (op Z₀))
      ((D.restrictionOverlapMap.app t).val.app (op Z₀))
      ((D.ambientOverlapMap.app t).val.app (op Z₀)) :=
  (D.isPullback_glueingKernel.map ((evaluation _ _).obj t)).map (SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS D.spaceX.1 D.spaceX.2).O)
    (op Z₀))

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- Reading the sections over `Z₀` of the `U`-component of `t` as global functions on `U'`, via
`eL`, is bijective. -/
theorem bijective_readingU :
    Function.Bijective (fun a : (D.restrictionDirectImage.obj t).val.obj (op Z₀) =>
      (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.openImmersion).map eL.hom).val.app (op Z₀) a))) :=
  (bijective_pushforwardUnitGlobal B S hS _ Z₀).comp
    ((bijective_val_app_apply_of_isIso B S hS
      ((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))
      (Iso.isIso_hom ((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).app _))
      Z₀).comp
      (bijective_val_app_apply_of_isIso B S hS
        ((modulePushforward B S hS D.openImmersion).map eL.hom) inferInstance Z₀))

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- Reading the sections over `Z₀` of the `Y`-component of `t` as global functions on `Y'`, via
`eR`, is bijective. -/
theorem bijective_readingY :
    Function.Bijective (fun b : (D.ambientDirectImage.obj t).val.obj (op Z₀) =>
      (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.ambientMorphism).map eR.hom).val.app (op Z₀) b))) :=
  (bijective_pushforwardUnitGlobal B S hS _ Z₀).comp
    ((bijective_val_app_apply_of_isIso B S hS
      ((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))
      (Iso.isIso_hom ((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).app _))
      Z₀).comp
      (bijective_val_app_apply_of_isIso B S hS
        ((modulePushforward B S hS D.ambientMorphism).map eR.hom) inferInstance Z₀))

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
include hγY in
/-- Reading the sections over `Z₀` of the overlap component of `t` as global functions on `V'`,
via `γ`, is bijective. -/
theorem bijective_readingV :
    Function.Bijective (fun c : (D.overlapDirectImage.obj t).val.obj (op Z₀) =>
      (pushforwardUnitGlobal B S hS
        (D.affLegVHom G ≫ D.openImmersionOver ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegVHom G)
          (D.openImmersionOver ≫ D.ambientMorphism)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G)))).val.app (op Z₀)
          (((modulePushforward B S hS (D.openImmersionOver ≫ D.ambientMorphism)).map γ).val.app
            (op Z₀) c))) := by
  have : IsIso γ := by rw [hγY]; infer_instance
  exact (bijective_pushforwardUnitGlobal B S hS _ Z₀).comp
    ((bijective_val_app_apply_of_isIso B S hS ((modulePushforwardCompIso B S hS (D.affLegVHom G)
          (D.openImmersionOver ≫ D.ambientMorphism)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G))))
      (Iso.isIso_hom ((modulePushforwardCompIso B S hS (D.affLegVHom G)
        (D.openImmersionOver ≫ D.ambientMorphism)).app _)) Z₀).comp
      (bijective_val_app_apply_of_isIso B S hS
        ((modulePushforward B S hS (D.openImmersionOver ≫ D.ambientMorphism)).map γ)
        inferInstance Z₀))

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The reading on `U'` of a kernel section through the composite morphism equals its reading
through the factors, the composition isomorphism applied last. -/
theorem readingU_kernel_comp (k : (D.glueingKernelDiagram.obj t).val.obj (op Z₀)) :
    (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        ((((D.glueingKernelFst.app t) ≫
            ((modulePushforward B S hS D.openImmersion).map eL.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))).val.app (op Z₀) k) =
      (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
          (((D.glueingKernelFst.app t) ≫
            ((modulePushforward B S hS D.openImmersion).map eL.hom)).val.app (op Z₀) k)) :=
  congrArg (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
    (compIso_comp_val_app_apply B S hS (D.affLegUHom G) D.openImmersion _
      (D.glueingKernelFst.app t ≫ (modulePushforward B S hS D.openImmersion).map eL.hom) Z₀ k)

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The reading on `U'` of a kernel section through the first projection followed by `eL` is
computed by applying the two maps in turn. -/
theorem readingU_kernel_split (k : (D.glueingKernelDiagram.obj t).val.obj (op Z₀)) :
    (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
          (((D.glueingKernelFst.app t) ≫
            ((modulePushforward B S hS D.openImmersion).map eL.hom)).val.app (op Z₀) k)) =
      (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.openImmersion).map eL.hom).val.app (op Z₀)
            ((D.glueingKernelFst.app t).val.app (op Z₀) k))) :=
  congrArg (fun z => (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
      (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀) z))
    (Stacks.SheafOfModules.comp_val_app_apply (D.glueingKernelFst.app t)
      ((modulePushforward B S hS D.openImmersion).map eL.hom) (op Z₀) k)

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The reading on `Y'` of a kernel section through the composite morphism equals its reading
through the factors, the composition isomorphism applied last. -/
theorem readingY_kernel_comp (k : (D.glueingKernelDiagram.obj t).val.obj (op Z₀)) :
    (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        ((((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))).val.app (op Z₀) k) =
      (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
          (((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)).val.app (op Z₀) k)) :=
  congrArg (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
    (compIso_comp_val_app_apply B S hS (D.affLegYHom G) D.ambientMorphism _
      (D.glueingKernelSnd.app t ≫ (modulePushforward B S hS D.ambientMorphism).map eR.hom) Z₀ k)

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
/-- The reading on `Y'` of a kernel section through the second projection followed by `eR` is
computed by applying the two maps in turn. -/
theorem readingY_kernel_split (k : (D.glueingKernelDiagram.obj t).val.obj (op Z₀)) :
    (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
          (((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)).val.app (op Z₀) k)) =
      (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.ambientMorphism).map eR.hom).val.app (op Z₀)
            ((D.glueingKernelSnd.app t).val.app (op Z₀) k))) :=
  congrArg (fun z => (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
      (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀) z))
    (Stacks.SheafOfModules.comp_val_app_apply (D.glueingKernelSnd.app t)
      ((modulePushforward B S hS D.ambientMorphism).map eR.hom) (op Z₀) k)

omit [IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀)] in
include hγY hγU in
/-- **The global sections of the module of Stacks 0AEX at a triple identified with
`(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})` are the glued ring**, semilinearly, through the two readings of
its projections as global functions on `U'` and on `Y'`. -/
theorem exists_kernelSectionsEquiv :
    ∃ κ : (D.glueingKernelDiagram.obj t).val.obj (op Z₀) → D.gluedFunctions G,
      Function.Bijective κ ∧ (∀ k₁ k₂, κ (k₁ + k₂) = κ k₁ + κ k₂) ∧
      (∀ (r : chartRing B S hS D.spaceX.1 D.spaceX.2 Z₀) k,
        κ (r • k) = D.gluedFunctionsAlgebraMap G Z₀ r * κ k) ∧
      (∀ k, (κ k).1.1 = (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        ((((D.glueingKernelFst.app t) ≫
            ((modulePushforward B S hS D.openImmersion).map eL.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))).val.app (op Z₀)
              k)) ∧
      (∀ k, (κ k).1.2 = (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        ((((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))).val.app (op Z₀)
              k)) := by
  obtain ⟨hw, hinj, hsurj⟩ :=
    isPullback_moduleCat_elements (D.sections_isPullback_glueingKernel Z₀ t)
  obtain ⟨hmem, hinj', hsurj'⟩ := fibreProduct_of_readings _ _ _ _ hw hinj hsurj _ _ _
    (D.bijective_readingU G Z₀ t eL) (D.bijective_readingY G Z₀ t eR)
    (D.bijective_readingV G Z₀ t eR γ hγY).1 (globalFunctionsMap B S hS (D.affLegVU G))
    (globalFunctionsMap B S hS (D.affLegVY G))
    (fun a => D.overlapReading_restrictionOverlapMap G Z₀ t eL.hom γ hγU a)
    (fun b => D.overlapReading_ambientOverlapMap G Z₀ t eR.hom γ hγY b)
  have hkU := D.readingU_kernel_comp G Z₀ t eL
  have hkU' := D.readingU_kernel_split G Z₀ t eL
  have hkY := D.readingY_kernel_comp G Z₀ t eR
  have hkY' := D.readingY_kernel_split G Z₀ t eR
  refine ⟨fun k => ⟨((pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.openImmersion).map eL.hom).val.app (op Z₀)
            ((D.glueingKernelFst.app t).val.app (op Z₀) k))),
      (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        (((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G)))).val.app (op Z₀)
          (((modulePushforward B S hS D.ambientMorphism).map eR.hom).val.app (op Z₀)
            ((D.glueingKernelSnd.app t).val.app (op Z₀) k)))),
      (D.mem_gluedFunctions G _).2 (hmem k)⟩,
    ⟨fun k k' h => hinj' k k' (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.1.2) h),
      fun z => ?_⟩, fun k k' => ?_, fun r k => ?_, fun k => ((hkU k).trans (hkU' k)).symm,
      fun k => ((hkY k).trans (hkY' k)).symm⟩
  · have hz : globalFunctionsMap B S hS (D.affLegVU G) z.1.1 =
        globalFunctionsMap B S hS (D.affLegVY G) z.1.2 := z.2
    obtain ⟨k, h1, h2⟩ := hsurj' z.1.1 z.1.2 hz
    exact ⟨k, Subtype.ext (Prod.ext h1 h2)⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact ((hkU (k + k')).trans (hkU' (k + k'))).symm.trans
        ((pushforwardUnitGlobal_comp_add B S hS (D.affLegUHom G) D.openImmersion Z₀
          ((D.glueingKernelFst.app t) ≫ ((modulePushforward B S hS D.openImmersion).map eL.hom))
          k k').trans (congrArg₂ (· + ·) ((hkU k).trans (hkU' k)) ((hkU k').trans (hkU' k'))))
    · exact ((hkY (k + k')).trans (hkY' (k + k'))).symm.trans
        ((pushforwardUnitGlobal_comp_add B S hS (D.affLegYHom G) D.ambientMorphism Z₀
          ((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom))
          k k').trans (congrArg₂ (· + ·) ((hkY k).trans (hkY' k)) ((hkY k').trans (hkY' k'))))
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine ((hkU (r • k)).trans (hkU' (r • k))).symm.trans
        ((pushforwardUnitGlobal_comp_smul B S hS (D.affLegUHom G) D.openImmersion Z₀
          ((D.glueingKernelFst.app t) ≫ ((modulePushforward B S hS D.openImmersion).map eL.hom))
          r k).trans ?_)
      refine (congrArg₂ (· * ·) (congrArg (fun φ => pullbackToGlobalFunctions B S hS (D.affLegU G)
        ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀) φ r) (D.affLegUToBase_eq G Z₀).symm)
        ((hkU k).trans (hkU' k))).trans ?_
      rw [Subring.coe_mul, Prod.fst_mul]
      rfl
    · refine ((hkY (r • k)).trans (hkY' (r • k))).symm.trans
        ((pushforwardUnitGlobal_comp_smul B S hS (D.affLegYHom G) D.ambientMorphism Z₀
          ((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)) r k).trans ?_)
      refine (congrArg₂ (· * ·) (congrArg (fun φ => pullbackToGlobalFunctions B S hS (D.affLegY G)
        ((SmallEtale.toOver B S hS D.spaceX.1).obj Z₀) φ r) (D.affLegYToBase_eq G Z₀).symm)
        ((hkY k).trans (hkY' k))).trans ?_
      rw [Subring.coe_mul, Prod.snd_mul]
      rfl

include hγY hγU in
/-- The global functions `Γ(Spec A)` are the global sections of the module of Stacks 0AEX at a
triple identified with `(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})`, as a module over `Γ(Z₀)`, compatibly with
the two readings of its projections. -/
theorem exists_gammaKernelEquiv :
    letI : Algebra (chartRing B S hS D.spaceX.1 D.spaceX.2 Z₀)
        Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) :=
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom.toAlgebra
    ∃ ι : Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) ≃ₗ[chartRing B S hS
        D.spaceX.1 D.spaceX.2 Z₀] (D.glueingKernelDiagram.obj t).val.obj (op Z₀),
      (∀ x, (pushforwardUnitGlobal B S hS (D.affLegUHom G ≫ D.openImmersion) Z₀)
        ((((D.glueingKernelFst.app t) ≫
            ((modulePushforward B S hS D.openImmersion).map eL.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegUHom G) D.openImmersion).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))).val.app (op Z₀)
              (ι x)) = D.gluedRingToLegU G Z₀ x) ∧
      (∀ x, (pushforwardUnitGlobal B S hS (D.affLegYHom G ≫ D.ambientMorphism) Z₀)
        ((((D.glueingKernelSnd.app t) ≫
            ((modulePushforward B S hS D.ambientMorphism).map eR.hom)) ≫
          ((modulePushforwardCompIso B S hS (D.affLegYHom G) D.ambientMorphism).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))).val.app (op Z₀)
              (ι x)) = D.gluedRingToLegY G Z₀ x) := by
  let : Algebra (chartRing B S hS D.spaceX.1 D.spaceX.2 Z₀)
      Γ((BigFppfOver.toScheme B S hS).obj (D.gluedObject G Z₀), ⊤) :=
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (D.gluedObjectHom G Z₀)).op).hom.toAlgebra
  obtain ⟨κ, hb, hadd, hsmul, hU, hY⟩ := D.exists_kernelSectionsEquiv G Z₀ t eL eR γ hγY hγU
  let κe := Equiv.ofBijective κ hb
  have hκe : ∀ x, κ (κe.symm x) = x := κe.apply_symm_apply
  have hκ' : ∀ y, κe y = κ y := fun _ => rfl
  refine ⟨{ toFun := fun x => κe.symm (D.gluedObjectGamma G Z₀ x)
            invFun := fun k => (D.gluedObjectGamma G Z₀).symm (κ k)
            left_inv := fun x => by simp [hκe]
            right_inv := fun k => by simp [κe]
            map_add' := fun x₁ x₂ => κe.injective (by
              rw [hκ', hκ', map_add, hκe, hadd, hκe, hκe])
            map_smul' := fun r x => κe.injective (by
              rw [hκ', hκ', hκe, RingHom.id_apply, hsmul, hκe, Algebra.smul_def, map_mul]
              exact congrArg (· * D.gluedObjectGamma G Z₀ x)
                (D.gluedObjectGamma_algebraMap G Z₀ r)) }, fun x => ?_, fun x => ?_⟩
  · refine (hU _).symm.trans ?_
    exact congrArg (fun p : D.gluedFunctions G => p.1.1) (hκe (D.gluedObjectGamma G Z₀ x))
  · refine (hY _).symm.trans ?_
    exact congrArg (fun p : D.gluedFunctions G => p.1.2) (hκe (D.gluedObjectGamma G Z₀ x))

end Triple

/-- **The comparison at one triple is an isomorphism**, from Stacks 0AF0: for a glueing triple of
modules `t` identified with `(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})` compatibly over `V`, the comparison
`G ⟶ F(Spec A)` is invertible as soon as the counit of Stacks 0AEY is. -/
theorem nonempty_gluedSpace_iso_of_triple (t : D.moduleGlueingData)
    (eL : (Comma.fst (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t.obj ≅
      (modulePushforward B S hS (D.affLegUHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegU G))))
    (eR : (Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).obj t.obj ≅
      (modulePushforward B S hS (D.affLegYHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegY G))))
    (γ : ((Comma.snd (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)) ⋙
        modulePullback B S hS D.openImmersionOver).obj t.obj ⟶
      (modulePushforward B S hS (D.affLegVHom G)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (D.affLegV G))))
    (hγY : γ = (modulePullback B S hS D.openImmersionOver).map eR.hom ≫
      (modulePullbackPushforwardUnitIso (D.isPullback_affLegVY G) G.property.2.2).hom)
    (hγU : (Comma.natTrans (modulePullback B S hS D.overlapRestriction)
        (modulePullback B S hS D.openImmersionOver)).app t.obj ≫ γ =
      (modulePullback B S hS D.overlapRestriction).map eL.hom ≫
        (modulePullbackPushforwardUnitIso (D.isPullback_affLegVU G) G.property.1).hom)
    (hcounit : IsIso D.glueingAdjunction.counit) :
    Nonempty ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀) ≅ G) := by
  obtain ⟨ι, hU, hY⟩ := D.exists_gammaKernelEquiv G Z₀ t.obj eL eR γ hγY hγU
  refine D.nonempty_iso_of_isIso_gluedLeft_gluedRight G Z₀ ?_ ?_
  · have := D.isIso_homEquiv_symm_glueingKernelFst t
    exact isIso_pullbackLift_of_counit D.openImmersion (D.affLegUHom G) G.property.1 Z₀
      (D.gluedObjectHom G Z₀) (D.gluedMapU G Z₀).1 (D.gluedMapU_hom_comp G Z₀)
      (D.glueingKernelDiagram.obj t.obj) (D.glueingKernelFunctor.obj t).property
      (D.glueingCounitLeft t ≫ eL.hom) inferInstance
      (D.glueingKernelFst.app t.obj ≫ (modulePushforward B S hS D.openImmersion).map eL.hom)
      (((modulePullbackAdjunction B S hS D.openImmersion).homEquiv_naturality_right _ _).trans
        (congrArg (· ≫ (modulePushforward B S hS D.openImmersion).map eL.hom)
          (homEquiv_glueingCounitLeft D t)))
      ⟨ι, fun x =>
        (hU x).trans (RingHom.congr_fun (D.pullbackToGlobalFunctions_gluedMapU G Z₀) x).symm⟩
  · have := D.isIso_glueingCounitRight_of_isIso_counit hcounit t
    exact isIso_pullbackLift_of_counit D.ambientMorphism (D.affLegYHom G) G.property.2.2 Z₀
      (D.gluedObjectHom G Z₀) (D.gluedMapY G Z₀).1 (D.gluedMapY_hom_comp G Z₀)
      (D.glueingKernelDiagram.obj t.obj) (D.glueingKernelFunctor.obj t).property
      (D.glueingCounitRight t ≫ eR.hom) inferInstance
      (D.glueingKernelSnd.app t.obj ≫ (modulePushforward B S hS D.ambientMorphism).map eR.hom)
      (((modulePullbackAdjunction B S hS D.ambientMorphism).homEquiv_naturality_right _ _).trans
        (congrArg (· ≫ (modulePushforward B S hS D.ambientMorphism).map eR.hom)
          (homEquiv_glueingCounitRight D t)))
      ⟨ι, fun x =>
        (hY x).trans (RingHom.congr_fun (D.pullbackToGlobalFunctions_gluedMapY G Z₀) x).symm⟩

/-- **The comparison at one triple is an isomorphism**, from Stacks 0AF0, at the module triple
`(g_{U*}𝒪_{U'}, g_{Y*}𝒪_{Y'})` of the glueing triple itself. -/
theorem nonempty_gluedSpace_iso (hcounit : IsIso D.glueingAdjunction.counit) :
    Nonempty ((affineGlueingFunctor D).obj (D.gluedSpace G Z₀) ≅ G) :=
  D.nonempty_gluedSpace_iso_of_triple G Z₀ (D.moduleTripleOfAffineLegs G) (Iso.refl _) (Iso.refl _)
    (modulePullbackPushforwardUnitIso (D.isPullback_affLegVY G) G.property.2.2).hom
    (by rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp])
    (by
      rw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      exact (Category.assoc _ _ _).trans (by rw [Iso.inv_hom_id, Category.comp_id])) hcounit

omit G in
/-- **Essential surjectivity in clause (1) of Stacks 0AF4 over an affine base, from Stacks 0AF0.**
If the ambient space `X` of a formal glueing situation is represented by an affine object `Z` of
the site and the unit and counit of the adjunction of Stacks 0AEY are invertible, then every
glueing triple with affine legs is the restriction of an algebraic space affine over `X`. -/
theorem essSurj_affineGlueingFunctor_of_isAffine {Z : BigFppfOver B S hS} (eX : D.X ≅ yoneda.obj Z)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (_hunit : IsIso D.glueingAdjunction.unit) (hcounit : IsIso D.glueingAdjunction.counit) :
    (affineGlueingFunctor D).EssSurj := by
  let Z₀ : SmallEtale B S hS D.spaceX.1 := representingChart B S hS D.spaceX Z eX
  have : IsIso Z₀.1.hom := inferInstanceAs (IsIso eX.inv)
  have : IsAffine ((SmallEtale.toOver B S hS D.spaceX.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
  exact ⟨fun G => ⟨D.gluedSpace G Z₀, D.nonempty_gluedSpace_iso G Z₀ hcounit⟩⟩


variable (B S hS) in
/-- **Essential surjectivity in clause (1) of Stacks 0AF4 over every affine base**: for every
formal glueing situation whose ambient space is an affine scheme, every glueing triple with affine
legs is the restriction of an algebraic space affine over the base. -/
theorem affineBaseEssSurj : AffineBaseEssSurj B S hS := by
  rintro D ⟨Z, hZ, ⟨eX⟩⟩
  exact D.essSurj_affineGlueingFunctor_of_isAffine eX D.isIso_glueingAdjunction_unit_counit.1
    D.isIso_glueingAdjunction_unit_counit.2

end AlgebraicGeometry.Space.FormalGlueingSituation
