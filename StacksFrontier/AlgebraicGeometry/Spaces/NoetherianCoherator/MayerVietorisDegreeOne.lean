module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.MayerVietorisVanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness

/-!
# Vanishing of the first higher direct image across an elementary distinguished square

Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square with intersection `P`, and
`h : W ⟶ Z` a morphism of algebraic spaces.  The degree-one case of the Mayer–Vietoris
induction cannot be read off the derived triangle alone: `R^1 h_*G` is the cokernel of the
degree-zero map `h_*(j_{U,*}G|_U ⊕ j_{V,*}G|_V) ⟶ h_*(j_{P,*}G|_P)`, and whether that map is onto
depends on the map itself.  This file proves, from the short exact sequence of Stacks 08GW
part (1), that `R^1 h_*G = 0` as soon as `R^1 a_*(G|_U) = 0`, `R^1 b_*(G|_V) = 0` and `h_*` of the
étale component `j_{V,*}G|_V ⟶ j_{P,*}G|_P` of the sequence is an epimorphism.

Two facts of homological algebra are isolated first.

* `CategoryTheory.Functor.isZero_rightDerived_one_of_shortExact`: for a left exact `F` and a
  short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `R^1 F(B) = 0` and `F(B) ⟶ F(C)` onto,
  `R^1 F(A) = 0`.
* `CategoryTheory.Functor.isZero_rightDerived_one_map_of_comp`: for `j` left exact preserving
  injective objects and `h` left exact, `R^1 (j ⋙ h)(M) = 0` forces `R^1 h(j M) = 0` — the
  injectivity of `R^1 h ∘ j ⟶ R^1(h ∘ j)` in the five-term sequence of the composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.Functor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A]

/-- **`R^1 F` vanishes on the subobject of a short exact sequence** whose middle term has
vanishing `R^1 F` and whose quotient map becomes an epimorphism after `F`, for a left exact
additive `F`: the connecting morphism `F(C) ⟶ R^1 F(A)` is then both zero and onto. -/
theorem isZero_rightDerived_one_of_shortExact (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (hB : IsZero ((F.rightDerived 1).obj S.X₂))
    (hg : Epi (F.map S.g)) : IsZero ((F.rightDerived 1).obj S.X₁) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  have hg0 : Epi ((D.functor 0).map S.g) := by
    change Epi ((F.rightDerived 0).map S.g)
    rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf S.g]
    infer_instance
  have : Epi (0 : (D.functor 0).obj S.X₃ ⟶ (D.functor (0 + 1)).obj S.X₁) :=
    (D.exact_δ₁ hS 0).epi_f_iff.1 hg0 ▸ (D.exact_δ₂ hS 0).epi_f (hB.eq_of_tgt _ _)
  exact IsZero.of_epi_zero ((D.functor 0).obj S.X₃) ((D.functor (0 + 1)).obj S.X₁)

/-- An additive left exact functor carries an epimorphism `R⁰F(g)` to an epimorphism `F(g)`, the
two being identified by `Functor.rightDerivedZeroIsoSelf`. -/
theorem epi_map_of_epi_rightDerived_zero_map (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {X Y : A} (g : X ⟶ Y) (hg : Epi ((F.rightDerived 0).map g)) : Epi (F.map g) := by
  rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf g]
  infer_instance

/-- **The injectivity of `R¹h ∘ j ⟶ R¹(h ∘ j)`**, in vanishing form.  For `j` additive, left
exact and preserving injective objects and `h` additive and left exact, `R¹(j ⋙ h)(M) = 0`
forces `R¹h(j M) = 0`.

Embed `M` into an injective `I` with cokernel `Q`.  The vanishing makes `(j ⋙ h)(I) ⟶ (j ⋙ h)(Q)`
onto; that map factors through `h` of the cokernel `C` of `j(M) ⟶ j(I)`, followed by `h` of the
monomorphism `C ⟶ j(Q)`, which is therefore invertible, so `h(j I) ⟶ h(C)` is onto; and `j I`
is injective, so the long exact sequence of `0 ⟶ j M ⟶ j I ⟶ C ⟶ 0` gives the claim. -/
theorem isZero_rightDerived_one_map_of_comp {A' : Type*} [Category* A'] [Abelian A']
    [EnoughInjectives A'] (j : A' ⥤ A) [j.Additive] [PreservesFiniteLimits j]
    [j.PreservesInjectiveObjects] (h : A ⥤ B) [h.Additive] [PreservesFiniteLimits h] (M : A')
    (hM : IsZero (((j ⋙ h).rightDerived 1).obj M)) :
    IsZero ((h.rightDerived 1).obj (j.obj M)) := by
  let := HasDerivedCategory.standard A'
  let := HasDerivedCategory.standard B
  let ι := Injective.ι M
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (j ⋙ h)
  have hF : Epi ((j ⋙ h).map (cokernel.π ι)) :=
    epi_map_of_epi_rightDerived_zero_map (j ⋙ h) _ ((D.exact_δ₁ hS 0).epi_f (hM.eq_of_tgt _ _))
  let m : cokernel (j.map ι) ⟶ j.obj (cokernel ι) :=
    cokernel.desc _ (j.map (cokernel.π ι)) (by rw [← j.map_comp, cokernel.condition, j.map_zero])
  have hm : Mono m :=
    (hS.exact.map_of_mono_of_preservesKernel j inferInstance inferInstance).mono_cokernelDesc
  let S' := ShortComplex.mk (j.map ι) (cokernel.π (j.map ι)) (cokernel.condition _)
  have hS' : S'.ShortExact := { exact := ShortComplex.exact_cokernel (j.map ι) }
  have hinj : Injective (j.obj (Injective.under M)) := j.injective_obj _
  have hfac : h.map (cokernel.π (j.map ι)) ≫ h.map m = (j ⋙ h).map (cokernel.π ι) := by
    rw [← h.map_comp, cokernel.π_desc, Functor.comp_map]
  have : Epi (h.map m) := epi_of_epi_fac hfac
  have : IsIso (h.map m) := isIso_of_mono_of_epi _
  exact isZero_rightDerived_one_of_shortExact h hS'
    (Functor.isZero_rightDerived_obj_injective_succ h 0 _)
    (by rwa [← epi_comp_iff_of_isIso _ (h.map m), hfac])

/-- The Mayer–Vietoris shape of `isZero_rightDerived_one_of_shortExact`: for a short exact
sequence `0 ⟶ X ⟶ Y₁ ⊞ Y₂ ⟶ Z ⟶ 0` whose second map is `(a, -b)`, `R¹F(X) = 0` as soon as
`R¹F(Y₁) = R¹F(Y₂) = 0` and `F(b)` is an epimorphism. -/
theorem isZero_rightDerived_one_of_shortExact_biprod (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] {X Y₁ Y₂ Z : A} {f : X ⟶ Y₁ ⊞ Y₂} {a : Y₁ ⟶ Z} {b : Y₂ ⟶ Z}
    {w : f ≫ biprod.desc a (-b) = 0} (hS : (ShortComplex.mk f (biprod.desc a (-b)) w).ShortExact)
    (h₁ : IsZero ((F.rightDerived 1).obj Y₁)) (h₂ : IsZero ((F.rightDerived 1).obj Y₂))
    (hb : Epi (F.map b)) : IsZero ((F.rightDerived 1).obj X) := by
  have := Stacks.DerivedLinear.rightDerived_additive F 1
  have hcomp : F.map biprod.inr ≫ F.map (biprod.desc a (-b)) = F.map b ≫ (-𝟙 _) := by
    rw [← Functor.map_comp, biprod.inr_desc, Functor.map_neg]
    simp
  exact isZero_rightDerived_one_of_shortExact F hS
    ((F.rightDerived 1).isZero_obj_biprod_of_isZero h₁ h₂) (epi_of_epi_fac hcomp)

end CategoryTheory.Functor

namespace CategoryTheory

section ConjugateComparison

variable {A D E : Type*} [Category* A] [Category* D] [Category* E]
  {rV : A ⥤ D} {pV : D ⥤ A} (adjV : rV ⊣ pV)
  {rS : D ⥤ E} {pS : E ⥤ D} (adjS : rS ⊣ pS)
  {rP : A ⥤ E} {pP : E ⥤ A} (adjP : rP ⊣ pP)
  {LV : D ⥤ A} (sV : LV ⊣ rV) {LP : E ⥤ A} (sP : LP ⊣ rP)
  (e : rV ⋙ rS ≅ rP)

/-- The comparison of left adjoints attached to a factorization `rV ⋙ rS ≅ rP` is the adjoint
transpose of the restricted unit, written out. -/
theorem factorLeftAdjointComparison_app_eq_map_factorUnit_comp_counit (F : A) :
    (Adjunction.factorLeftAdjointComparison rV rS rP e sP sV).app F =
      LP.map ((Adjunction.factorUnit rV rS rP e sV).app F) ≫ sP.counit.app ((rV ⋙ LV).obj F) := by
  rw [← Adjunction.homEquiv_factorLeftAdjointComparison_app rV rS rP e sP sV F,
    Adjunction.homEquiv_unit]
  simp

/-- The identity in `E` behind `conjugateEquiv_factorLeftAdjointComparison_app`: both sides are
`e⁻¹ ≫ rS(ε_V) ≫ e`. -/
theorem factorUnit_comp_map_eq_restrictionUnit_comp (G : A) :
    rP.map (pV.map (adjS.unit.app (rV.obj G))) ≫ e.inv.app (pV.obj (pS.obj (rS.obj (rV.obj G)))) ≫
        rS.map (adjV.counit.app (pS.obj (rS.obj (rV.obj G)))) ≫
          adjS.counit.app (rS.obj (rV.obj G)) ≫ e.hom.app G =
      (Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G)) ≫
        rP.map (LV.map (adjV.counit.app (rV.obj G))) ≫ rP.map (sV.counit.app G) := by
  have hL : rP.map (pV.map (adjS.unit.app (rV.obj G))) ≫
        e.inv.app (pV.obj (pS.obj (rS.obj (rV.obj G)))) ≫
        rS.map (adjV.counit.app (pS.obj (rS.obj (rV.obj G)))) ≫
          adjS.counit.app (rS.obj (rV.obj G)) ≫ e.hom.app G =
      e.inv.app (pV.obj (rV.obj G)) ≫ rS.map (adjV.counit.app (rV.obj G)) ≫ e.hom.app G := by
    have h1 := e.inv.naturality (pV.map (adjS.unit.app (rV.obj G)))
    simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h1
    rw [← Category.assoc, h1, Category.assoc]
    simp only [Functor.id_obj, ← rS.map_comp_assoc, Adjunction.counit_naturality]
    simp
  have hR : (Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G)) ≫
        rP.map (LV.map (adjV.counit.app (rV.obj G))) ≫ rP.map (sV.counit.app G) =
      e.inv.app (pV.obj (rV.obj G)) ≫ rS.map (adjV.counit.app (rV.obj G)) ≫ e.hom.app G := by
    rw [Adjunction.factorUnit_app]
    have h2 := e.hom.naturality (LV.map (adjV.counit.app (rV.obj G)) ≫ sV.counit.app G)
    simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h2
    rw [← rP.map_comp, Category.assoc, Category.assoc, ← h2]
    simp only [← rS.map_comp_assoc, rV.map_comp, Functor.id_obj]
    simp
  exact hL.trans hR.symm

/-- **The conjugate of the comparison of left adjoints attached to a factorization is the
pushforward of the restriction unit.**  For `rP ≅ rV ⋙ rS`, with right adjoints `pV`, `pS`, `pP`
and left adjoints `LV ⊣ rV`, `LP ⊣ rP`, the conjugate `rV ⋙ pV ⟶ rP ⋙ pP` of the comparison
`rP ⋙ LP ⟶ rV ⋙ LV` is `pV` applied to the unit of `rS ⊣ pS`, followed by the canonical
isomorphism `pS ⋙ pV ≅ pP` and `pP` of `e`. -/
theorem conjugateEquiv_factorLeftAdjointComparison_app (G : A) :
    (conjugateEquiv (adjV.comp sV) (adjP.comp sP)
      (Adjunction.factorLeftAdjointComparison rV rS rP e sP sV)).app G =
      pV.map (adjS.unit.app (rV.obj G)) ≫
        (conjugateEquiv (adjV.comp adjS) adjP e.inv).app (rS.obj (rV.obj G)) ≫
          pP.map (e.hom.app G) := by
  have hL : (conjugateEquiv (adjV.comp sV) (adjP.comp sP)
      (Adjunction.factorLeftAdjointComparison rV rS rP e sP sV)).app G =
      adjP.unit.app (pV.obj (rV.obj G)) ≫ pP.map
        ((Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G)) ≫
          rP.map (LV.map (adjV.counit.app (rV.obj G))) ≫ rP.map (sV.counit.app G)) := by
    have aux : sP.unit.app (rP.obj (pV.obj (rV.obj G))) ≫
        rP.map (LP.map ((Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G))) ≫
          sP.counit.app (LV.obj (rV.obj (pV.obj (rV.obj G))))) =
        (Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G)) := by
      have hn := sP.unit.naturality ((Adjunction.factorUnit rV rS rP e sV).app (pV.obj (rV.obj G)))
      simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
      rw [rP.map_comp, ← Category.assoc, ← hn, Category.assoc, sP.right_triangle_components,
        Category.comp_id]
    rw [conjugateEquiv_apply_app]
    simp only [Adjunction.comp_unit_app, Adjunction.comp_counit_app, Functor.comp_map,
      Functor.comp_obj, factorLeftAdjointComparison_app_eq_map_factorUnit_comp_counit,
      Category.assoc]
    congr 1
    rw [← pP.map_comp_assoc, aux, ← pP.map_comp, rP.map_comp]
  have hR : pV.map (adjS.unit.app (rV.obj G)) ≫
        (conjugateEquiv (adjV.comp adjS) adjP e.inv).app (rS.obj (rV.obj G)) ≫
          pP.map (e.hom.app G) =
      adjP.unit.app (pV.obj (rV.obj G)) ≫ pP.map
        (rP.map (pV.map (adjS.unit.app (rV.obj G))) ≫
          e.inv.app (pV.obj (pS.obj (rS.obj (rV.obj G)))) ≫
          rS.map (adjV.counit.app (pS.obj (rS.obj (rV.obj G)))) ≫
            adjS.counit.app (rS.obj (rV.obj G)) ≫ e.hom.app G) := by
    rw [conjugateEquiv_apply_app]
    simp only [Adjunction.comp_counit_app, Functor.comp_obj, Functor.map_comp, Category.assoc]
    rw [← adjP.unit_naturality_assoc]
    rfl
  rw [hL, hR, factorUnit_comp_map_eq_restrictionUnit_comp]

end ConjugateComparison

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  isGrothendieckAbelian_modules etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance 5000] modulePushforward_additive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image along an étale morphism preserves injective objects: its left adjoint, the
restriction, is exact. -/
theorem preservesInjectiveObjects_modulePushforward_of_isEtale {X Y : AlgebraicSpaces B S hS}
    (i : Y ⟶ X) (hi : IsEtale B S hS i.hom) :
    (modulePushforward B S hS i).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleModulePullbackAdjunction B S hS i hi)

/-- `R¹h_*(j_*M) = 0` as soon as `R¹(j ≫ h)_*M = 0`, for `j` étale. -/
theorem isZero_rightDerived_one_modulePushforward_obj_of_isEtale {X Y Z : AlgebraicSpaces B S hS}
    (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) (h : X ⟶ Z) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : IsZero (((modulePushforward B S hS (j ≫ h)).rightDerived 1).obj M)) :
    IsZero (((modulePushforward B S hS h).rightDerived 1).obj
      ((modulePushforward B S hS j).obj M)) := by
  have := preservesInjectiveObjects_modulePushforward_of_isEtale B S hS j hj
  have := preservesFiniteLimits_modulePushforward B S hS j
  have := preservesFiniteLimits_modulePushforward B S hS h
  exact Functor.isZero_rightDerived_one_map_of_comp _ _ M <| hM.of_iso
    ((Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (modulePushforwardCompIso B S hS j h) 1).app M)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {Z : AlgebraicSpaces B S hS} (h : W ⟶ Z)

/-- **The degree-one step of a higher-direct-image vanishing across an elementary distinguished
square.**  `R¹h_*G = 0` as soon as `R¹a_*(G|_U) = 0`, `R¹b_*(G|_V) = 0` and `h_*` carries the étale
component `j_{V,*}(G|_V) ⟶ j_{P,*}(G|_P)` of the Mayer–Vietoris sequence to an epimorphism. -/
theorem isZero_rightDerived_one_of_eds (G : Modules.{u, u} B S hS W.1 W.2)
    (hU : IsZero (((modulePushforward B S hS (edsOpenHom B S hS hsq ≫ h)).rightDerived 1).obj
        ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq)).obj G)))
    (hV : IsZero (((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ h)).rightDerived 1).obj
        ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).obj G)))
    (hepi : Epi ((modulePushforward B S hS h).map
      ((conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq))).app G))) :
    IsZero (((modulePushforward B S hS h).rightDerived 1).obj G) := by
  have := preservesFiniteLimits_modulePushforward B S hS h
  exact Functor.isZero_rightDerived_one_of_shortExact_biprod (modulePushforward B S hS h)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq G)
    (isZero_rightDerived_one_modulePushforward_obj_of_isEtale B S hS _
      (isEtale_edsOpenHom B S hS hsq) h _ hU)
    (isZero_rightDerived_one_modulePushforward_obj_of_isEtale B S hS _
      (isEtale_edsEtaleHom B S hS hsq) h _ hV) hepi

/-- **`h_*` of the étale component of the Mayer–Vietoris sequence is onto** as soon as
`b_*` of the restriction unit `G|_V ⟶ q_*(G|_P)` along `q : P ⟶ V` is, `b` being the
restriction of `h` to `V`: by `CategoryTheory.conjugateEquiv_factorLeftAdjointComparison_app`
the étale component is `j_{V,*}` of that unit followed by isomorphisms. -/
theorem epi_modulePushforward_map_conjugate_edsShriekEtaleComparison
    (G : Modules.{u, u} B S hS W.1 W.2)
    (hη : Epi ((modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ h)).map
      ((etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).unit.app
          ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj G)))) :
    Epi ((modulePushforward B S hS h).map
      ((conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq))).app G)) := by
  have key : (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq))).app G = _ :=
    conjugateEquiv_factorLeftAdjointComparison_app
      (edsAdjEtale B S hS hsq) (etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)) (edsAdjInter B S hS hsq)
      (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq)
      (edsFactorIsoEtale B S hS hsq) G
  rw [key, Functor.map_comp, Functor.map_comp]
  have e1 : (modulePushforward B S hS h).map ((modulePushforward B S hS
      (edsEtaleHom B S hS hsq)).map ((etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).unit.app ((etaleModulePullback.{u, u} B S hS
          (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj G))) =
      (modulePushforwardCompIso B S hS (edsEtaleHom B S hS hsq) h).hom.app _ ≫
        (modulePushforward B S hS (edsEtaleHom B S hS hsq ≫ h)).map
          ((etaleModulePullbackAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).unit.app ((etaleModulePullback.{u, u} B S hS
              (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj G)) ≫
        (modulePushforwardCompIso B S hS (edsEtaleHom B S hS hsq) h).inv.app _ :=
    (NatIso.naturality_2 (modulePushforwardCompIso B S hS (edsEtaleHom B S hS hsq) h) _).symm
  rw [e1]
  exact epi_comp' (epi_comp' (IsIso.epi_of_iso _) (epi_comp' hη (IsIso.epi_of_iso _)))
    (epi_comp' (IsIso.epi_of_iso _) (IsIso.epi_of_iso _))

end Square

end AlgebraicGeometry.Space

end
