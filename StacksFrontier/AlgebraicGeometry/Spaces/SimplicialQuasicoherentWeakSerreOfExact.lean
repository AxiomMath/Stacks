module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleQuasicoherentWeakSerre

/-!
# Quasi-coherent modules on an fppf hypercovering form a weak Serre subcategory, given exactness

Let `a : U → X` be an fppf hypercovering of an algebraic space by a simplicial algebraic space and
`a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` the morphism of ringed topoi of Stacks 0DE7.
If `a^*` is exact, the quasi-coherent `𝒪_U`-modules form a weak Serre subcategory: by
Stacks 0DHD every quasi-coherent `𝒪_U`-module is `a^*F` with `F` quasi-coherent, the counit
`a^*a_*G ⟶ G` being invertible, so kernels and cokernels come from `X`, where quasi-coherence is a
weak Serre class; for an extension, `R¹a_*` vanishes on the first term (Stacks 0DHE), so `a_*`
keeps the sequence exact and the five lemma makes the counit invertible at the middle term.

## Main results

* `Adjunction.shortExact_map_and_isIso_counit_app_X₂_simplicialQuasicoherentWeakSerreOfExact`:
  the counit at the middle term of an extension is invertible.
* `isWeakSerreClass_isQuasicoherentOnSite_ringedSite_of_preservesFiniteLimits`: quasi-coherent
  `𝒪_U`-modules form a weak Serre subcategory when `a^*` is exact.

## References

* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 0DHD](https://stacks.math.columbia.edu/tag/0DHD)
* [Stacks Project, Tag 0DHE](https://stacks.math.columbia.edu/tag/0DHE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.Adjunction

/-- **The counit at the middle term of an extension.** Let `L ⊣ R` with `L` exact, and let
`0 → S₁ → S₂ → S₃ → 0` be short exact with `R¹R(S₁) = 0`. Then `R` keeps the sequence short
exact, and if the counit is invertible at `S₁` and `S₃` it is invertible at `S₂`. -/
theorem shortExact_map_and_isIso_counit_app_X₂_simplicialQuasicoherentWeakSerreOfExact
    {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives C] {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex C} (hS : S.ShortExact) (h₁ : IsIso (adj.counit.app S.X₁))
    (h₃ : IsIso (adj.counit.app S.X₃)) (hR : IsZero ((R.rightDerived 1).obj S.X₁)) :
    (S.map R).ShortExact ∧ IsIso (adj.counit.app S.X₂) := by
  have : L.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : PreservesFiniteLimits R :=
    have : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
    inferInstance
  have hT := Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one R hS hR
  refine ⟨hT, ?_⟩
  have hS₁ : ((S.map R).map L).ShortExact := hT.map_of_exact L
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  have : IsIso φ.τ₁ := h₁
  have : IsIso φ.τ₃ := h₃
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS₁ hS

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

variable (U) in
/-- Modules on `U_{spaces,étale}` have enough injectives, at the ringed-site spelling. -/
local instance enoughInjectives_ringedSiteModules_weakSerreOfExact :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite U).J)
        (ringedSite U).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (U) in
/-- Modules on `U_{spaces,étale}` have enough injectives, at the ringed-topos spelling. -/
local instance enoughInjectives_ringedToposModules_weakSerreOfExact :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- **Quasi-coherence on an fppf hypercovering is a weak Serre class, once `a^*` is exact.** -/
theorem isWeakSerreClass_isQuasicoherentOnSite_ringedSite_of_preservesFiniteLimits
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)
    [hex : PreservesFiniteLimits
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom)] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite U).J)
        (ringedSite U).O)).IsWeakSerreClass := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite U).J)
        (ringedSite U).O)
  let QX := SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
        (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X))
  let adj := RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (augmentationRingedToposHom a)
  let Ap := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom
  let Aq := RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (augmentationRingedToposHom a)
  have hd := descent_quasicoherent_of_isHypercoveringAugmentation h
  have hexAp : PreservesFiniteLimits Ap := hex
  have : QX.IsWeakSerreClass :=
    isWeakSerreClass_isQuasicoherentOnSite_spacesEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
      T.schemeSite S T.scheme_mem X
  have := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a)
  have : PreservesFiniteLimits Aq :=
    have : PreservesLimitsOfSize.{0, 0} Aq := adj.rightAdjoint_preservesLimits
    inferInstance
  have : PreservesFiniteColimits Ap :=
    have : PreservesColimitsOfSize.{0, 0} Ap := adj.leftAdjoint_preservesColimits
    inferInstance
  have : Ap.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : Aq.IsRightAdjoint := ⟨_, ⟨adj⟩⟩
  have : Aq.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isRightAdjoint _
  have : Ap.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have hP : P.IsClosedUnderIsomorphisms := inferInstance
  have key : ∀ G, P G → QX (Aq.obj G) ∧ IsIso (adj.counit.app G) := fun G hG ↦
    ⟨hd.2.1 G hG, hd.2.2.2 G hG⟩
  have back : ∀ G, QX (Aq.obj G) → IsIso (adj.counit.app G) → P G := fun G hG hc ↦
    P.prop_of_iso (@asIso _ _ _ _ (adj.counit.app G) hc) (hd.1 _ hG)
  let ciso : ∀ G, P G → Iso (Ap.obj (Aq.obj G)) G := fun G hG ↦
    @asIso _ _ _ _ _ (hd.2.2.2 G hG)
  have hz : P.ContainsZero := inferInstance
  have hker : P.IsClosedUnderKernels :=
    { kernels_le := by
        rintro _ ⟨f, k, hk, hf⟩
        have hK : QX (kernel (Aq.map f)) := QX.prop_kernel _ (hd.2.1 _ hf.1) (hd.2.1 _ hf.2)
        exact P.prop_of_iso (PreservesKernel.iso Ap (Aq.map f) ≪≫
          kernel.mapIso _ f (ciso _ hf.1) (ciso _ hf.2) (adj.counit.naturality f) ≪≫
          IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk) (hd.1 _ hK) }
  have hcoker : P.IsClosedUnderCokernels :=
    { cokernels_le := by
        rintro _ ⟨f, k, hk, hf⟩
        have hK : QX (cokernel (Aq.map f)) := QX.prop_cokernel _ (hd.2.1 _ hf.1) (hd.2.1 _ hf.2)
        exact P.prop_of_iso (PreservesCokernel.iso Ap (Aq.map f) ≪≫
          cokernel.mapIso _ f (ciso _ hf.1) (ciso _ hf.2) (adj.counit.naturality f) ≪≫
          IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk) (hd.1 _ hK) }
  have hext : P.IsClosedUnderExtensions :=
    { prop_X₂_of_shortExact := by
        intro T' hT h1 h3
        obtain ⟨q1, c1⟩ := key _ h1
        obtain ⟨q3, c3⟩ := key _ h3
        have hR : IsZero ((Aq.rightDerived 1).obj T'.X₁) := by
          have : (Aq.obj T'.X₁).IsQuasicoherentOnSite := q1
          exact (isZero_rightDerived_augmentationRingedToposHom_pushforwardModules_pullbackModules
            h (Aq.obj T'.X₁) 1 one_pos).of_iso
              ((Aq.rightDerived 1).mapIso (@asIso _ _ _ _ _ c1)).symm
        obtain ⟨hT', c2⟩ :=
          adj.shortExact_map_and_isIso_counit_app_X₂_simplicialQuasicoherentWeakSerreOfExact
            hT c1 c3 hR
        exact back _ (QX.prop_X₂_of_shortExact hT' q1 q3) c2 }
  exact { }

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
