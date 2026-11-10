module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.DifferentIdeal
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.FlatCase
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.OneMemComplementaryModule
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProjectiveTraceContraction
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticSupport
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat

/-!
# The different on an affine chart is the Dedekind different

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes with
relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`, and let `V = Spec B` and
`U = Spec A` be affine opens with `f(V) ⊆ U`.  If the Dedekind different of `A → B` is defined,
then the different `𝔇_f` of Tag 0BW4 agrees on `V` with the Dedekind different `𝔇_{B/A}` of
Tag 0BW1.

## Main results

* `Stacks.Discriminant.different_obj_affine_eq_dedekindDifferentIdeal`: the sections of `𝔇_f`
  over the affine chart `V` are the Dedekind different ideal of `Γ(X, U) → Γ(Y, V)`.

## Implementation notes

Tag 0BW5 states the conclusion as an equality `𝔇_f|_V = (𝔇_{B/A})~` of coherent ideal sheaves
on `V`.  The different is coherent (`Stacks.Discriminant.isCoherent_different`) and a coherent
sheaf on an affine scheme is the tilde of its module of sections, so that equality holds exactly
when the two ideals of sections over `V` agree; the statement below is that equality of ideals
of `Γ(Y, V)`, which is the same content without any transport of sheaves along `V ≅ Spec B`.

The proof is the Stacks one.  The different is the annihilator of the cokernel of
`τ_{Y/X} : 𝒪_Y → ω_{Y/X}`, and on a coherent module over an affine open the sections of the
annihilator sheaf are the annihilator of the module of sections.  On the chart the map
`Γ(Y, V) → Γ(ω_{Y/X}, V)` becomes `B → Hom_A(B, A)`, `1 ↦ Tr_{B/A}`: the identification of
`Γ(ω_{Y/X}, V)` with `Hom_A(B, A)` is the factorization of `A → B` through itself
(`Stacks.Discriminant.selfFactorization`), and the image of the trace element is the ordinary
trace by uniqueness of trace elements (Tag 0BT7) together with Tag 0BT8.  Tag 0BW3 then says
that the annihilator of `Hom_A(B, A) / B·Tr_{B/A}` is the Dedekind different ideal.

## References

* [Stacks Project, Tag 0BW5](https://stacks.math.columbia.edu/tag/0BW5)
* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
* [Stacks Project, Tag 0BW3](https://stacks.math.columbia.edu/tag/0BW3)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
  RingedSpaceModuleAdjunction TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u v

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-! ### The generic-fibre trace of a flat finite algebra -/

section Algebraic

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- In the setup for the Dedekind different of a flat finite algebra, the generic-fibre trace
of an element of `B` is the image in `Q(A)` of its finite-projective trace over `A`. -/
private theorem trace_algebraMap_eq_map_finiteProjectiveTrace
    (setup : DedekindDifferentSetup A B) [Module.Flat A B] (b : B) :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    letI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
    letI : Module.Projective A B := Module.Flat.projective_of_finitePresentation
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) =
      algebraMap A (FractionRing A)
        (finiteProjectiveTrace A B ((Algebra.lmul A B).toLinearMap b)) := by
  classical
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  let K := FractionRing A
  let L := B ⊗[A] K
  let M := K ⊗[A] B
  let F := Fin n → A
  let FK := K ⊗[A] F
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let : Algebra K M := Algebra.TensorProduct.leftAlgebra
  let bFK : Module.Basis (Fin n) K FK :=
    Algebra.TensorProduct.basis K (Pi.basisFun A (Fin n))
  let : Module.Free K FK := Module.Free.of_basis bFK
  let : Module.Finite K FK := Module.Finite.of_basis bFK
  let e : M ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K M := Module.Finite.base_change A K B
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  let iK : M →ₗ[K] FK := i.baseChange K
  let pK : FK →ₗ[K] M := p.baseChange K
  let iL : L →ₗ[K] FK := iK.comp e.symm.toLinearMap
  let pL : FK →ₗ[K] L := e.toLinearMap.comp pK
  have hpiL : pL.comp iL = LinearMap.id := LinearMap.ext fun z => by
    change e (((p.baseChange K).comp (i.baseChange K)) (e.symm z)) = z
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
    exact e.apply_symm_apply z
  let : Module.Projective K L := Module.Projective.of_split iL pL hpiL
  let μ : B →ₗ[A] B := Algebra.lmul A B b
  let r : F →ₗ[A] F := i.comp (μ.comp p)
  let μK : M →ₗ[K] M := μ.baseChange K
  let x : L := algebraMap B L b
  let T : L →ₗ[K] L := Algebra.lmul K L x
  have heμ : e.symm.toLinearMap.comp (T.comp e.toLinearMap) = μK := by
    have hx : x = e (1 ⊗ₜ[A] b) := by
      change algebraMap B (B ⊗[A] K) b =
        Algebra.TensorProduct.commRight A K B (1 ⊗ₜ[A] b)
      simp
    rw [show μK = Algebra.lmul K M (1 ⊗ₜ[A] b) from Algebra.baseChange_lmul b]
    apply LinearMap.ext
    intro q
    induction q using TensorProduct.inductionOn with
    | tmul k y =>
      change e.symm (x * e (k ⊗ₜ[A] y)) = (1 ⊗ₜ[A] b) * (k ⊗ₜ[A] y)
      rw [hx]
      apply e.injective
      simp
    | add q q' hq hq' => rw [map_add, map_add, hq, hq']
  have hcomp : iL.comp (T.comp pL) = r.baseChange K := by
    calc
      iL.comp (T.comp pL) =
          iK.comp ((e.symm.toLinearMap.comp (T.comp e.toLinearMap)).comp pK) := by
        simp [iL, pL, LinearMap.comp_assoc]
      _ = iK.comp (μK.comp pK) := by rw [heμ]
      _ = r.baseChange K := by
        dsimp [iK, pK, μK, r, μ]
        rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]
  change contractLeft K L ((dualTensorHomEquiv K L L).symm T) =
    algebraMap A K (finiteProjectiveTrace A B μ)
  rw [← finiteProjectiveTrace_eq_contract (R := K) (P := L) T,
    finiteProjectiveTrace_eq_trace_of_split K L FK pL iL hpiL T, hcomp,
    LinearMap.trace_baseChange r K,
    finiteProjectiveTrace_eq_trace_of_split A B F p i hpi μ]

/-- The Dedekind different ideal of a flat finite algebra is the annihilator of the quotient of
the relative dualizing module `Hom_A(B, A)` by the `B`-line generated by the trace
functional. -/
private theorem annihilator_dual_quotient_eq_dedekindDifferentIdeal_of_flat
    (setup : DedekindDifferentSetup A B) [Module.Flat A B] :
    Module.annihilator B
      (Module.Dual A B ⧸ Submodule.span B
        { complementaryModuleEquivDualizingModule setup
            ⟨1, one_mem_complementaryModule_of_flat setup⟩ }) =
      dedekindDifferentIdeal setup :=
  annihilator_dual_quotient_eq_dedekindDifferentIdeal setup
    (one_mem_complementaryModule_of_flat setup)

/-- For a module-finite algebra the relative dualizing module of the identity factorization is
`Hom_A(B, A) ⊗_B B`, hence canonically `Hom_A(B, A)`. -/
def selfFactorizationDualEquiv [Module.Finite A B] :
    dualizingModule (selfFactorization A B) ≃ₗ[B] Module.Dual A B := by
  let eAdd : (Module.Dual A B ⊗[B] B) ≃+ Module.Dual A B :=
    (TensorProduct.comm B (Module.Dual A B) B).toAddEquiv.trans
      (TensorProduct.lid B (Module.Dual A B)).toAddEquiv
  refine { toAddEquiv := eAdd, map_smul' := fun c x => ?_ }
  change TensorProduct.lid B (Module.Dual A B)
      ((TensorProduct.comm B (Module.Dual A B) B).toAddEquiv
        ((TensorProduct.comm B (Module.Dual A B) B).toAddEquiv.symm
          (c • (TensorProduct.comm B (Module.Dual A B) B).toAddEquiv x))) = _
  simp [eAdd]
  rfl

/-- The trace element of a finite flat algebra becomes, under the canonical identification of
the relative dualizing module with `Hom_A(B, A)`, the image of `1` under the trace-pairing
identification of the complementary module. -/
private theorem selfFactorizationDualEquiv_finiteFlatTraceElement
    (setup : DedekindDifferentSetup A B) [Module.Flat A B] :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    selfFactorizationDualEquiv (finiteFlatTraceElement A B) =
      complementaryModuleEquivDualizingModule setup
        ⟨1, one_mem_complementaryModule_of_flat setup⟩ := by
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  refine LinearMap.ext fun b => ?_
  apply IsFractionRing.injective A (FractionRing A)
  calc
    algebraMap A (FractionRing A)
        (selfFactorizationDualEquiv (A := A) (B := B) (finiteFlatTraceElement A B) b) =
        algebraMap A (FractionRing A)
          (finiteProjectiveTrace A B ((Algebra.lmul A B).toLinearMap b)) := by
      congr 1
      change ((TensorProduct.lid B (Module.Dual A B))
        ((TensorProduct.comm B (Module.Dual A B) B)
          (((finiteProjectiveTrace A B).comp
            (Algebra.lmul A B).toLinearMap) ⊗ₜ (1 : B)))) b = _
      simp only [TensorProduct.comm_tmul, TensorProduct.lid_tmul, one_smul]
      rfl
    _ = setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) :=
      (trace_algebraMap_eq_map_finiteProjectiveTrace setup b).symm
    _ = _ := (complementaryModuleEquivDualizingModule_one_apply setup b).symm

end Algebraic

/-! ### Sections of a quasi-coherent module over an affine open -/

section Affine

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf Scheme.Modules

/-- The global sections of the restriction of a module to the spectrum of the coordinate ring of
an affine open are the sections of the module over that open. -/
def specGammaToOpenEquiv {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (M : X.Modules) [IsOpenImmersion hU.fromSpec] :
    moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let N := M.restrict hU.fromSpec
  let Q := modulesSpecToSheaf.obj N
  have hImage : U = hU.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let eTopAb : Γ(N, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso hU.fromSpec ⊤ ≪≫ M.presheaf.mapIso (eqToIso hImage).op
  let eTop0 : Q.presheaf.obj (.op ⊤) ≃+ Γ(M, U) := eTopAb.addCommGroupIsoToAddEquiv
  let eRing : Γ(X, hU.fromSpec ''ᵁ ⊤) ≅ Γ(X, U) := X.presheaf.mapIso (eqToIso hImage).op
  have hR (a : Γ(X, U)) :
      eRing.hom ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = a := by
    have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv = (hU.fromSpec.appIso ⊤).hom := by
      simp only [eRing, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appIso_hom']
      have hAppLE : hU.fromSpec.appLE U ⊤ (by simp [hU.fromSpec_preimage_self]) =
          (Scheme.ΓSpecIso Γ(X, U)).inv := by
        simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
        simp
      rw [← hAppLE]
      simpa only [eqToIso.hom] using (hU.fromSpec.map_appLE' (V := ⊤) (by simp) hImage)
    have hAEq' : eRing.hom = (hU.fromSpec.appIso ⊤).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
      rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hAEq', ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  have htop (a : Γ(X, U)) (m : Γ(N, ⊤)) : eTop0 (a • m) = a • eTop0 m := by
    change eTopAb.hom (a • m) = a • eTopAb.hom m
    rw [Scheme.Modules.smul_Spec_def]
    rw [show (Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op = 𝟙 _ from rfl]
    simp only [CategoryTheory.id_apply, eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Functor.mapIso_hom, Iso.op_hom] at *
    rw [M.map_smul]
    congr 1
    exact hR a
  let eTop : Γ(N, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) := { eTop0 with map_smul' := htop }
  change Q.presheaf.obj (.op ⊤) ≃ₗ[Γ(X, U)] Γ(M, U)
  exact eTop

/-- The identification of the global sections over the spectrum with the sections over the
affine open is natural in the module. -/
theorem specGammaToOpenEquiv_map {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {M N : X.Modules} [IsOpenImmersion hU.fromSpec]
    (φ : M ⟶ N) (m : moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) :
    specGammaToOpenEquiv hU N
        (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hU.fromSpec).map φ) m) =
      φ.app U (specGammaToOpenEquiv hU M m) := by
  let j := hU.fromSpec
  have hImage : U = j ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let eTopAbM : Γ(M.restrict j, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso j ⊤ ≪≫ M.presheaf.mapIso (eqToIso hImage).op
  let eTopAbN : Γ(N.restrict j, ⊤) ≅ Γ(N, U) :=
    N.restrictAppIso j ⊤ ≪≫ N.presheaf.mapIso (eqToIso hImage).op
  change eTopAbN.hom (((Scheme.Modules.restrictFunctor j).map φ).app ⊤ m) =
    φ.app U (eTopAbM.hom m)
  dsimp [eTopAbM, eTopAbN]
  simp only [Scheme.Modules.restrictAppIso]
  exact congr($(φ.val.naturality ((eqToIso hImage).hom.op)) m).symm

/-- Global sections on an affine scheme carry the cokernel of a map of quasi-coherent modules to
the cokernel of the map of modules of sections. -/
def specCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    moduleSpecΓFunctor.obj (cokernel φ) ≅ cokernel (moduleSpecΓFunctor.map φ) := by
  let eM := asIso (Scheme.Modules.fromTildeΓ M)
  let eN := asIso (Scheme.Modules.fromTildeΓ N)
  have hnat : (tilde.functor R).map (moduleSpecΓFunctor.map φ) ≫ eN.hom = eM.hom ≫ φ :=
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  exact moduleSpecΓFunctor.mapIso
    (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map φ) ≪≫
      cokernel.mapIso _ φ eM eN hnat).symm ≪≫ (tilde.isoTop _).symm

/-- On an affine open the sections of the annihilator sheaf of a coherent module are the
annihilator of the module of sections. -/
theorem annihilatorSheaf_obj_eq_annihilator {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (U : X.affineOpens) :
    (show Ideal Γ(X, U.1) from
        (Stacks.SheafOfModules.annihilatorSheaf X.toRingedSpace F).toSubmodule.obj (op U.1)) =
      Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
  obtain ⟨I, -, hI, hU⟩ := exists_isCoherent_submodule_eq_annihilatorIdeal F
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  rw [← hI]
  exact (hU U).symm.trans (annihilatorIdeal_ideal F U)

end Affine

/-! ### The different on an affine chart -/

section Comparison

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf Scheme.Modules

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

/-- **[Stacks, Tag 0BW5].** Let `f : Y → X` be a flat quasi-finite morphism of locally
Noetherian schemes and let `V = Spec B ⊆ Y` and `U = Spec A ⊆ X` be affine opens with
`f(V) ⊆ U`.  If the Dedekind different of `A → B` is defined, then the sections of the different
`𝔇_f` over `V` are the Dedekind different ideal `𝔇_{B/A} ⊆ B`.

Both `𝔇_f` and the ideal sheaf associated with `𝔇_{B/A}` are coherent ideal sheaves on the
affine `V`, and a coherent sheaf on an affine scheme is the tilde of its module of sections; so
this equality of ideals of `B` is the assertion that `𝔇_f|_V = (𝔇_{B/A})~`. -/
@[stacks 0BW5]
theorem different_obj_affine_eq_dedekindDifferentIdeal (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ setup : DedekindDifferentSetup Γ(X, U.1) Γ(Y, V.1),
      (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
        dedekindDifferentIdeal setup := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  intro setup
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Finite Γ(X, U.1) Γ(Y, V.1) := setup.finite
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Module.FinitePresentation Γ(X, U.1) Γ(Y, V.1) :=
    Module.finitePresentation_of_finite Γ(X, U.1) Γ(Y, V.1)
  let : Module.Projective Γ(X, U.1) Γ(Y, V.1) := Module.Flat.projective_of_finitePresentation
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let φ := traceMorphism ω τ
  have hωq : ω.sheaf.IsQuasicoherent := ω.isQuasicoherent
  have hωc : ω.sheaf.IsCoherent := ω.isCoherent
  have hunit : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  have hunitq : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (SheafOfModules.unit Y.ringCatSheaf)).1
  have hcok : (cokernel φ).IsCoherent :=
    @_root_.SheafOfModules.cokernel_isCoherent _ _ _ _ _ hunit hωc φ
  have hD : (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
      Module.annihilator Γ(Y, V.1) Γ(cokernel φ, V.1) :=
    @annihilatorSheaf_obj_eq_annihilator Y _ (cokernel φ) hcok V
  let j := V.2.fromSpec
  let : IsOpenImmersion j := V.2.isOpenImmersion_fromSpec
  let R : CommRingCat := CommRingCat.of Γ(Y, V.1)
  let FΓ := moduleSpecΓFunctor (R := R)
  let fSpec := (Scheme.Modules.restrictFunctor j).map φ
  let OSpec := (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf)
  let MSpec := (Scheme.Modules.restrictFunctor j).obj ω.sheaf
  let : OSpec.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j _
  let : MSpec.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j _
  let F := selfFactorization Γ(X, U.1) Γ(Y, V.1)
  let eO : FΓ.obj OSpec ≃ₗ[Γ(Y, V.1)] Γ(Y, V.1) :=
    specGammaToOpenEquiv V.2 (SheafOfModules.unit Y.ringCatSheaf)
  let eM : FΓ.obj MSpec ≃ₗ[Γ(Y, V.1)] Module.Dual Γ(X, U.1) Γ(Y, V.1) :=
    ((specGammaToOpenEquiv V.2 ω.sheaf).trans (ω.localEquiv U V hVU F)).trans
      selfFactorizationDualEquiv
  have hle : V.1 ≤ ⊤ := le_top
  let t : Module.Dual Γ(X, U.1) Γ(Y, V.1) :=
    complementaryModuleEquivDualizingModule setup
      ⟨1, one_mem_complementaryModule_of_flat setup⟩
  have hf : eM (FΓ.map fSpec (eO.symm 1)) = t := by
    change selfFactorizationDualEquiv
      (ω.localEquiv U V hVU F
        (specGammaToOpenEquiv V.2 ω.sheaf (FΓ.map fSpec (eO.symm 1)))) = t
    rw [specGammaToOpenEquiv_map V.2 φ (eO.symm 1)]
    have hOne : specGammaToOpenEquiv V.2 (SheafOfModules.unit Y.ringCatSheaf) (eO.symm 1) =
        (1 : Γ(Y, V.1)) := eO.apply_symm_apply 1
    rw [hOne]
    have htr : ((φ.val.app (op V.1)).hom) (1 : Γ(Y, V.1)) =
        (ω.sheaf.presheaf.map (homOfLE hle).op).hom τ.sect :=
      traceMorphism_app_one ω τ V.1
    change selfFactorizationDualEquiv
      (ω.localEquiv U V hVU F (((φ.val.app (op V.1)).hom) (1 : Γ(Y, V.1)))) = t
    rw [htr]
    have hunique : ω.localEquiv U V hVU F
        (restrictₗ ω.sheaf hle τ.sect) =
        finiteFlatTraceElement Γ(X, U.1) Γ(Y, V.1) :=
      isTraceElement_unique F (τ.isTraceElement_localEquiv U V hVU F)
        (isTraceElement_finiteFlatTraceElement Γ(X, U.1) Γ(Y, V.1))
    rw [show (ω.sheaf.presheaf.map (homOfLE hle).op).hom τ.sect =
      restrictₗ ω.sheaf hle τ.sect from rfl, hunique]
    exact selfFactorizationDualEquiv_finiteFlatTraceElement setup
  let fΓ := FΓ.map fSpec
  let eOi := eO.toModuleIso
  let eMi := eM.toModuleIso
  let g : ModuleCat.of R R ⟶ ModuleCat.of R (Module.Dual Γ(X, U.1) Γ(Y, V.1)) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  have hfg : fΓ ≫ eMi.hom = eOi.hom ≫ g := by
    apply (cancel_epi eOi.symm.hom).mp
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    refine LinearMap.ext fun r => ?_
    have hr : eOi.symm.hom r = r • eOi.symm.hom 1 := by
      simpa using eOi.symm.hom.hom.map_smul r (1 : Γ(Y, V.1))
    change eM (fΓ (eOi.symm.hom r)) = LinearMap.toSpanSingleton R _ t (eOi.hom (eOi.symm.hom r))
    rw [hr]
    change eM (fΓ.hom (r • eOi.symm.hom 1)) = _
    calc
      _ = r • t := by rw [fΓ.hom.map_smul, eM.map_smul]; exact congrArg (fun x => r • x) hf
      _ = LinearMap.toSpanSingleton R _ t (eOi.hom (r • eOi.symm.hom 1)) := by
        rw [eOi.hom.hom.map_smul, show eOi.hom (eOi.symm.hom (1 : Γ(Y, V.1))) = 1 by simp]
        simp [LinearMap.toSpanSingleton_apply]
  let cIso := cokernel.mapIso fΓ g eOi eMi hfg
  let qIso := ModuleCat.cokernelIsoRangeQuotient g
  let eC : (Scheme.Modules.restrictFunctor j).obj (cokernel φ) ≅ cokernel fSpec :=
    PreservesCokernel.iso (Scheme.Modules.restrictFunctor j) φ
  let eCSection : FΓ.obj (cokernel fSpec) ≃ₗ[Γ(Y, V.1)] Γ(cokernel φ, V.1) :=
    ((FΓ.mapIso eC.symm).toLinearEquiv).trans (specGammaToOpenEquiv V.2 (cokernel φ))
  let eQ : Γ(cokernel φ, V.1) ≃ₗ[Γ(Y, V.1)]
      (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸ LinearMap.range (LinearMap.toSpanSingleton R _ t)) :=
    eCSection.symm.trans (specCokernelIso fSpec).toLinearEquiv |>.trans cIso.toLinearEquiv
      |>.trans qIso.toLinearEquiv
  calc
    (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
        Module.annihilator Γ(Y, V.1) Γ(cokernel φ, V.1) := hD
    _ = Module.annihilator Γ(Y, V.1)
        (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸
          LinearMap.range (LinearMap.toSpanSingleton R _ t)) := eQ.annihilator_eq
    _ = Module.annihilator Γ(Y, V.1)
        (Module.Dual Γ(X, U.1) Γ(Y, V.1) ⧸ Submodule.span Γ(Y, V.1) {t}) := by
      rw [LinearMap.range_toSpanSingleton]
    _ = dedekindDifferentIdeal setup :=
      annihilator_dual_quotient_eq_dedekindDifferentIdeal_of_flat setup

end Comparison

end Stacks.Discriminant

end
