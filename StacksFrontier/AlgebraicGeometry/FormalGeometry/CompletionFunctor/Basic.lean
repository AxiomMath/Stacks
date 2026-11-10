module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Completion of a coherent module along a quasi-coherent ideal sheaf

Let `X` be a locally Noetherian scheme and `I` a quasi-coherent ideal sheaf on `X`. Quotienting a
coherent module `F` by the successive subsheaves `I ^ (n+1) F` produces an inverse system
`n ↦ F / I ^ (n+1) F` of coherent modules. Each term is annihilated by `I ^ (n+1)`, and the
transition map exhibits the `n`-th term as the quotient of the `(n+1)`-st by that same power, so
the system is a coherent adic system in the sense of `Stacks.Coherent.IsCoherentAdicSystem`. The
construction is functorial, and the resulting functor `Coh(𝒪_X) ⥤ Coh(X, I)` is the completion
functor of Stacks 0880.

## Main definitions

* `Stacks.Algebraization.completionFunctor` — the completion functor.
* `Stacks.Algebraization.completionProjection` — the canonical map from a coherent module onto the
  `n`-th term of its completion.

## Main results

* `Stacks.Algebraization.completionFunctor_obj` — the `n`-th term is the quotient by `I ^ (n+1)`.
* `Stacks.Algebraization.completionProjection_transition` — the projections are compatible with
  the transition maps of the inverse system.
* `Stacks.Algebraization.completionFunctor_map_quotient` — the map the functor assigns to a
  morphism is the induced map on the successive quotients.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι sectionsModuleΓPresheaf

/-- The projection `M ⟶ M / N` onto the quotient by a subsheaf `N` is an epimorphism. -/
local instance epi_cokernelπ_submodule {X : Scheme.{u}} {M : X.Modules}
    (N : SheafOfModules.Submodule M) :
    Epi (cokernel.π (C := X.Modules) N.ι) :=
  coequalizer.π_epi

open Scheme.Modules TopologicalSpace

/-! ### An epimorphism of quasi-coherent modules is surjective on affine sections -/

/-- On the spectrum of a ring, an epimorphism of quasi-coherent modules is surjective on global
sections. -/
private theorem epi_app_top_surjective_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (f : M ⟶ N) [Epi f] : Function.Surjective (f.app ⊤) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, hM⟩
  let N' : P.FullSubcategory := ⟨N, hN⟩
  let f' : M' ⟶ N' := ObjectProperty.homMk f
  have hf' : Epi f' := ⟨fun g h hh =>
    ObjectProperty.hom_ext P ((cancel_epi f).1 (congrArg (ObjectProperty.ι P).map hh))⟩
  let e := tildeEquiv (R := R)
  exact (ModuleCat.epi_iff_surjective (e.inverse.map f')).mp (e.inverse.map_epi f')

/-- The restriction of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private theorem isQuasicoherent_restrictFunctor_obj {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g]
    {M : X.Modules} (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor g).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app M).symm
    (Stacks.Modules.isQuasicoherent_pullback g M hM)

/-- On an affine scheme, an epimorphism of quasi-coherent modules is surjective on global
sections. -/
private theorem epi_app_top_surjective_affine {Y : Scheme.{u}}
    [IsAffine Y] {M N : Y.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent)
    (f : M ⟶ N) [Epi f] : ∀ s : Γ(N, ⊤), ∃ x : Γ(M, ⊤), f.app ⊤ x = s := by
  let e := Y.isoSpec
  let M' := (Scheme.Modules.restrictFunctor e.inv).obj M
  let N' := (Scheme.Modules.restrictFunctor e.inv).obj N
  have hs := epi_app_top_surjective_spec (isQuasicoherent_restrictFunctor_obj e.inv hM)
    (isQuasicoherent_restrictFunctor_obj e.inv hN)
    ((Scheme.Modules.restrictFunctor e.inv).map f)
  have htop : e.inv ''ᵁ (⊤ : (Spec Γ(Y, ⊤)).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  intro s
  let s' := N.presheaf.map (eqToHom htop).op s
  obtain ⟨x, hx⟩ := hs s'
  refine ⟨M.presheaf.map (eqToHom htop.symm).op x, ?_⟩
  have hx' : f.app ⊤ (M.presheaf.map (eqToHom htop.symm).op x) =
      N.presheaf.map (eqToHom htop.symm).op (f.app (e.inv ''ᵁ ⊤) x) :=
    congrArg (fun q => q x) (f.mapPresheaf.naturality (eqToHom htop.symm).op)
  have hx2 : f.app (e.inv ''ᵁ ⊤) x = s' := hx
  refine hx'.trans ?_
  simpa [s', ← Functor.map_comp] using congrArg (N.presheaf.map (eqToHom htop.symm).op) hx2

/-- An epimorphism of quasi-coherent modules is surjective on the sections over any affine open. -/
private theorem epi_app_affineOpen_surjective {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (A : X.affineOpens)
    (f : F ⟶ G) [Epi f] (s : Γ(G, A)) : ∃ t : Γ(F, A), f.app A t = s := by
  let FA := (Scheme.Modules.restrictFunctor A.1.ι).obj F
  let GA := (Scheme.Modules.restrictFunctor A.1.ι).obj G
  have hsurj := epi_app_top_surjective_affine
    (isQuasicoherent_restrictFunctor_obj A.1.ι ‹F.IsQuasicoherent›)
    (isQuasicoherent_restrictFunctor_obj A.1.ι ‹G.IsQuasicoherent›)
    ((Scheme.Modules.restrictFunctor A.1.ι).map f)
  let htop := A.1.ι_image_top
  let sA : Γ(GA, ⊤) := (G.restrictAppIso A.1.ι ⊤).inv
    (G.presheaf.map (eqToHom htop).op s)
  obtain ⟨tA, htA⟩ := hsurj sA
  let tA' := (F.restrictAppIso A.1.ι ⊤).hom tA
  refine ⟨F.presheaf.map (eqToHom htop.symm).op tA', ?_⟩
  have hcomm : (G.restrictAppIso A.1.ι ⊤).hom
      (((Scheme.Modules.restrictFunctor A.1.ι).map f).app ⊤ tA) =
        f.app (A.1.ι ''ᵁ ⊤) ((F.restrictAppIso A.1.ι ⊤).hom tA) := by rfl
  have htA' := congrArg (fun z => (G.restrictAppIso A.1.ι ⊤).hom z) htA
  rw [hcomm] at htA'
  have hs' : (G.restrictAppIso A.1.ι ⊤).hom sA = G.presheaf.map (eqToHom htop).op s := by
    simp [sA]
  have hn : f.app A.1 (F.presheaf.map (eqToHom htop.symm).op tA') =
      G.presheaf.map (eqToHom htop.symm).op (f.app (A.1.ι ''ᵁ ⊤) tA') :=
    congrArg (fun q => q tA') (f.mapPresheaf.naturality (eqToHom htop.symm).op)
  refine hn.trans ?_
  rw [htA', hs']
  simp

/-! ### Coherence and quasi-coherence of the successive quotients -/

/-- On a locally Noetherian scheme, a quasi-coherent quotient of a coherent module is coherent. -/
private lemma coherent_of_quasicoherent_quotient
    {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    (hM : M.IsCoherent) (hN : N.IsQuasicoherent) (f : M ⟶ N) [Epi f] :
    N.IsCoherent := by
  have : M.IsCoherent := hM
  have : N.IsQuasicoherent := hN
  have : M.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).2
  have hepi : Epi (C := SheafOfModules.{u} X.ringCatSheaf) f :=
    ⟨fun g h hh => (cancel_epi (C := X.Modules) f).1 hh⟩
  have : N.IsFiniteType := Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} f inferInstance
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType N

/-- The quotient `M / I ^ n M` of a quasi-coherent module is quasi-coherent. -/
private lemma idealPowerQuotient_isQuasicoherent
    {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] :
    (idealPowerQuotient I n M).IsQuasicoherent :=
  let : (idealPowerMultiple I n M).toSheafOfModules.IsQuasicoherent :=
    idealPowerMultiple_isQuasicoherent I n M
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _

/-- The quotient `M / I ^ n M` of a coherent module is coherent. -/
private lemma idealPowerQuotient_isCoherent
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) [M.IsCoherent] [M.IsQuasicoherent] :
    (idealPowerQuotient I n M).IsCoherent :=
  coherent_of_quasicoherent_quotient (M := M) inferInstance
    (idealPowerQuotient_isQuasicoherent I n M)
    (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι)

/-- The quotient `M / I ^ n M` of a quasi-coherent module is annihilated by `I ^ n`. An alias of
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot`. -/
private alias idealPowerMultiple_eq_bot_idealPowerQuotient :=
  idealPowerMultiple_idealPowerQuotient_eq_bot

/-! ### Preimages of subsheaves, and the induced maps on quotients -/

/-- A morphism carries `I ^ n M` into the preimage of any subsheaf containing `I ^ n N`. -/
private lemma idealPowerMultiple_le_comapLocal {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (hq : idealPowerMultiple I n N ≤ Q) :
    idealPowerMultiple I n M ≤ _root_.AlgebraicGeometry.sheafSubmoduleComap f Q := by
  refine (idealPowerMultiple_le_iff I n M _).2 fun U => ?_
  set J := I.ideal U ^ n with hJ
  set fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := ModuleCat.Hom.hom (f.val.app (op U.1)) with hfU
  change J • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤ (Q.toSubmodule.obj (op U.1)).comap fU
  calc
    J • (⊤ : Submodule Γ(X, U) Γ(M, U)) =
        J • ((⊤ : Submodule Γ(X, U) Γ(N, U)).comap fU) := by simp
    _ ≤ (J • (⊤ : Submodule Γ(X, U) Γ(N, U))).comap fU :=
      Submodule.smul_comap_le_comap_smul fU _ _
    _ ≤ (Q.toSubmodule.obj (op U.1)).comap fU :=
      Submodule.comap_mono ((idealPowerMultiple_le_iff I n N Q).mp hq U)

/-- The ideal-power subsheaves are monotone in the ideal power. -/
private lemma idealPowerMultiple_le_of_ideal_pow_le
    {X : Scheme.{u}} {I J : X.IdealSheafData} (m n : ℕ)
    (h : J ^ n ≤ I ^ m) (M : X.Modules) :
    idealPowerMultiple J n M ≤ idealPowerMultiple I m M := by
  refine (idealPowerMultiple_le_iff J n M _).2 fun U => ?_
  exact (Submodule.smul_mono_left (h U)).trans ((idealPowerMultiple_le_iff I m M _).1 le_rfl U)

/-- A morphism carries `J ^ n M` into the preimage of `I ^ m N` whenever `J ^ n ≤ I ^ m`. -/
private lemma idealPowerMultiple_le_comap_of_pow_le
    {X : Scheme.{u}} (I J : X.IdealSheafData) (m n : ℕ)
    (hpow : J ^ n ≤ I ^ m) {M N : X.Modules} (f : M ⟶ N) :
    idealPowerMultiple J n M ≤
      _root_.AlgebraicGeometry.sheafSubmoduleComap f (idealPowerMultiple I m N) := by
  refine (idealPowerMultiple_le_comapLocal J n f (idealPowerMultiple J n N) le_rfl).trans ?_
  have hpow'' : (idealPowerMultiple J n N).toSubmodule ≤ (idealPowerMultiple I m N).toSubmodule :=
    SheafOfModules.Submodule.le_iff.mp (idealPowerMultiple_le_of_ideal_pow_le m n hpow N)
  exact SheafOfModules.Submodule.le_iff.mpr fun U => Submodule.comap_mono (hpow'' U)

/-- The map on sheaf quotients induced by a morphism which carries one submodule into the
other. -/
private def quotientMapOfHom
    {X : Scheme.{u}} {M N : X.Modules} {S : M.Submodule} {T : N.Submodule}
    (f : M ⟶ N) (h : S ≤ _root_.AlgebraicGeometry.sheafSubmoduleComap f T) :
    cokernel (C := X.Modules) S.ι ⟶ cokernel (C := X.Modules) T.ι :=
  cokernel.desc (C := X.Modules) S.ι (f ≫ cokernel.π (C := X.Modules) T.ι)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ cokernel.π (C := X.Modules) T.ι)
            (_root_.AlgebraicGeometry.sheafSubmoduleMap_comp_ι f S T h)).symm.trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => _root_.AlgebraicGeometry.sheafSubmoduleMap f S T h ≫ k)
              (cokernel.condition (C := X.Modules) T.ι)).trans comp_zero))))

/-- The induced map on quotients commutes with the quotient projections. -/
private lemma quotientMapOfHom_π
    {X : Scheme.{u}} {M N : X.Modules} {S : M.Submodule} {T : N.Submodule}
    (f : M ⟶ N) (h : S ≤ _root_.AlgebraicGeometry.sheafSubmoduleComap f T) :
    cokernel.π (C := X.Modules) S.ι ≫ quotientMapOfHom f h =
      f ≫ cokernel.π (C := X.Modules) T.ι :=
  cokernel.π_desc _ _ _

/-- The map `M / J ^ n M ⟶ N / I ^ m N` induced by a morphism `M ⟶ N` when `J ^ n ≤ I ^ m`. -/
private def quotientMapOfHom_idealPowers
    {X : Scheme.{u}} (I J : X.IdealSheafData) (m n : ℕ)
    (hpow : J ^ n ≤ I ^ m) {M N : X.Modules} (f : M ⟶ N) :
    idealPowerQuotient J n M ⟶ idealPowerQuotient I m N :=
  quotientMapOfHom f (idealPowerMultiple_le_comap_of_pow_le I J m n hpow f)

/-- The induced map on ideal-power quotients commutes with the quotient projections. -/
private lemma quotientMapOfHom_idealPowers_π
    {X : Scheme.{u}} (I J : X.IdealSheafData) (m n : ℕ)
    (hpow : J ^ n ≤ I ^ m) {M N : X.Modules} (f : M ⟶ N) :
    cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι ≫
        quotientMapOfHom_idealPowers I J m n hpow f =
      f ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I m N).ι :=
  quotientMapOfHom_π f _

/-- The induced map on ideal-power quotients is an epimorphism when the given morphism is. -/
private lemma quotientMapOfHom_idealPowers_epi
    {X : Scheme.{u}} (I J : X.IdealSheafData) (m n : ℕ)
    (hpow : J ^ n ≤ I ^ m) {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi (quotientMapOfHom_idealPowers I J m n hpow f) := by
  have : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι ≫
      quotientMapOfHom_idealPowers I J m n hpow f) := by
    rw [quotientMapOfHom_idealPowers_π]
    infer_instance
  exact epi_of_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J n M).ι) _

/-- The identity induces the identity on ideal-power quotients. -/
private lemma quotientMapOfHom_idealPowers_id
    {X : Scheme.{u}} (J : X.IdealSheafData) (r : ℕ) (M : X.Modules) :
    quotientMapOfHom_idealPowers J J r r le_rfl (𝟙 M) = 𝟙 _ := by
  refine coequalizer.hom_ext ?_
  rw [quotientMapOfHom_idealPowers_π]
  simp

/-- The induced maps on ideal-power quotients compose. -/
private lemma quotientMapOfHom_idealPowers_comp
    {X : Scheme.{u}} (J : X.IdealSheafData) (r : ℕ)
    {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    quotientMapOfHom_idealPowers J J r r le_rfl (f ≫ g) =
      quotientMapOfHom_idealPowers J J r r le_rfl f ≫
        quotientMapOfHom_idealPowers J J r r le_rfl g := by
  refine coequalizer.hom_ext ?_
  simp only [← Category.assoc, quotientMapOfHom_idealPowers_π]
  simp only [Category.assoc, quotientMapOfHom_idealPowers_π]

/-! ### The transition isomorphism -/

/-- When `I ^ r M` vanishes the quotient projection `M ⟶ M / I ^ r M` is an isomorphism. -/
private lemma idealPowerQuotientProjection_isIso_of_eq_bot
    {X : Scheme.{u}} (J : X.IdealSheafData) (r : ℕ) (M : X.Modules)
    (hbot : idealPowerMultiple J r M = ⊥) :
    IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple J r M).ι) := by
  rw [hbot]
  refine cokernel.π_of_zero (C := X.Modules) ?_
  ext U x
  exact (Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj M (op U)).le x.property)

/-- Taking the quotient of `M / I ^ r M` by `I ^ r` again changes nothing. -/
private lemma quotientProjection_idealPowerQuotient_isIso
    {X : Scheme.{u}} (J : X.IdealSheafData) (r : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (cokernel.π (C := X.Modules)
      (idealPowerMultiple J r (idealPowerQuotient J r M)).ι) :=
  idealPowerQuotientProjection_isIso_of_eq_bot J r _
    (idealPowerMultiple_eq_bot_idealPowerQuotient J r M)

/-- The map `M / I ^ s M ⟶ (M / I ^ s M) / J ^ r (M / I ^ s M)` induced by the projection
`M ⟶ M / I ^ s M` is an isomorphism when `I ^ s ≤ J ^ r`. -/
private lemma quotientMapOfHom_idealPowers_quotient_isIso
    {X : Scheme.{u}} (J I : X.IdealSheafData) (r s : ℕ)
    (hpow : I ^ s ≤ J ^ r) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (quotientMapOfHom_idealPowers J J r r le_rfl
      (cokernel.π (C := X.Modules) (idealPowerMultiple I s M).ι)) := by
  let qI : M ⟶ idealPowerQuotient I s M :=
    cokernel.π (C := X.Modules) (idealPowerMultiple I s M).ι
  let qJ : M ⟶ idealPowerQuotient J r M :=
    cokernel.π (C := X.Modules) (idealPowerMultiple J r M).ι
  let u : idealPowerQuotient I s M ⟶ idealPowerQuotient J r M :=
    quotientMapOfHom_idealPowers J I r s hpow (𝟙 M)
  let qbar := quotientMapOfHom_idealPowers J J r r le_rfl qI
  let ubar := quotientMapOfHom_idealPowers J J r r le_rfl u
  let jbar := quotientMapOfHom_idealPowers J J r r le_rfl qJ
  have hqu : qI ≫ u = qJ := by
    dsimp only [qI, qJ, u]
    rw [quotientMapOfHom_idealPowers_π]
    simp
  have hcomp : qbar ≫ ubar = jbar := by
    dsimp only [qbar, ubar, jbar]
    rw [← quotientMapOfHom_idealPowers_comp, hqu]
  have hjbar : IsIso jbar := by
    have : IsIso (cokernel.π (C := X.Modules)
        (idealPowerMultiple J r (idealPowerQuotient J r M)).ι) :=
      quotientProjection_idealPowerQuotient_isIso J r M
    have hj : jbar = cokernel.π (C := X.Modules)
        (idealPowerMultiple J r (idealPowerQuotient J r M)).ι := by
      refine coequalizer.hom_ext ?_
      dsimp only [jbar, qJ]
      rw [quotientMapOfHom_idealPowers_π]
    rw [hj]
    infer_instance
  have : Epi qbar := quotientMapOfHom_idealPowers_epi J J r r le_rfl qI
  have : Mono (qbar ≫ ubar) := by rw [hcomp]; infer_instance
  have : Mono qbar := mono_of_mono qbar ubar
  exact isIso_of_mono_of_epi qbar

/-- The reindexing `n ↦ n + 1` of the index category of the inverse system. -/
private def completionIndexShift : ℕᵒᵖ ⥤ ℕᵒᵖ where
  obj n := op (n.unop + 1)
  map f := (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse system `n ↦ M / I ^ (n+1) M`, the shift of the ideal-power tower. -/
private def completionQuotientSystem
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) : ℕᵒᵖ ⥤ X.Modules :=
  completionIndexShift ⋙ adicQuotientSystem I M

/-- The `n`-th term of the shifted tower is the quotient by `I ^ (n+1)`. -/
private theorem completionQuotientSystem_obj
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) (n : ℕ) :
    (completionQuotientSystem I M).obj (op n) = idealPowerQuotient I (n + 1) M :=
  rfl

/-- The quotient projections are compatible with the transition maps of the shifted tower. -/
private theorem completionQuotientSystem_projection_arrow
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) {i j : ℕᵒᵖ} (g : i ⟶ j) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I (i.unop + 1) M).ι ≫
        (completionQuotientSystem I M).map g =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (j.unop + 1) M).ι := by
  have h := quotientMapOfLE_π
    (idealPowerMultiple_antitone I M (leOfHom (completionIndexShift.map g).unop))
  simpa [adicQuotientSystem, completionIndexShift, completionQuotientSystem] using h

/-- The quotient projections are compatible with the transition maps, in the numeric form. -/
private theorem completionQuotientSystem_projection
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) {i j : ℕ} (h : j ≤ i) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I (i + 1) M).ι ≫
        (completionQuotientSystem I M).map (homOfLE h).op =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (j + 1) M).ι :=
  completionQuotientSystem_projection_arrow I M (homOfLE h).op

/-- Quotienting the `(n+1)`-st term of the shifted tower by `I ^ (n+1)` gives back the `n`-th. -/
private def completionQuotientIso
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    idealPowerQuotient I (n + 1) (idealPowerQuotient I (n + 2) M) ≅
      idealPowerQuotient I (n + 1) M :=
  letI := quotientMapOfHom_idealPowers_quotient_isIso I I (n + 1) (n + 2)
    (fun U => by
      rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
      exact Ideal.pow_le_pow_right (by omega)) M
  (asIso (quotientMapOfHom_idealPowers I I (n + 1) (n + 1) le_rfl
    (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 2) M).ι))).symm

/-- Under the transition isomorphism, the canonical quotient projection is the transition map of
the shifted tower. -/
private theorem completionQuotientIso_hom_comp
    {X : Scheme.{u}} (I : X.IdealSheafData) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    cokernel.π (C := X.Modules)
          (idealPowerMultiple I (n + 1) (idealPowerQuotient I (n + 2) M)).ι ≫
        (completionQuotientIso I M n).hom =
      (completionQuotientSystem I M).map (homOfLE (Nat.le_succ n)).op := by
  let q : M ⟶ idealPowerQuotient I (n + 2) M :=
    cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 2) M).ι
  have hqbar := quotientMapOfHom_idealPowers_quotient_isIso I I (n + 1) (n + 2)
    (fun U => by
      rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
      exact Ideal.pow_le_pow_right (by omega)) M
  let qbar := quotientMapOfHom_idealPowers I I (n + 1) (n + 1) le_rfl q
  let e := (asIso qbar).symm
  have he : qbar ≫ e.hom = 𝟙 _ := (asIso qbar).hom_inv_id
  have h1 : cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M).ι ≫ qbar =
      q ≫ cokernel.π (C := X.Modules)
        (idealPowerMultiple I (n + 1) (idealPowerQuotient I (n + 2) M)).ι :=
    quotientMapOfHom_idealPowers_π I I (n + 1) (n + 1) le_rfl q
  refine (cancel_epi q).1 (Eq.trans ?_ (completionQuotientSystem_projection I M
    (Nat.le_succ n)).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom) h1).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => cokernel.π (C := X.Modules)
            (idealPowerMultiple I (n + 1) M).ι ≫ k) he).trans (Category.comp_id _))))

/-! ### The completion functor -/

/-- The shifted tower of a coherent module is a coherent adic system. -/
private theorem completionAdicSystem_property
    {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    Stacks.Coherent.IsCoherentAdicSystem I (completionQuotientSystem I F.obj) := by
  have : F.obj.IsCoherent := F.property
  have : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  exact ⟨fun n => idealPowerQuotient_isCoherent I (n + 1) F.obj,
    fun n => idealPowerMultiple_eq_bot_idealPowerQuotient I (n + 1) F.obj,
    fun n => ⟨completionQuotientIso I F.obj n, completionQuotientIso_hom_comp I F.obj n⟩⟩

/-- The morphism of shifted towers induced by a morphism of coherent modules. -/
private def completionAdicMap
    {X : Scheme.{u}} (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G) :
    completionQuotientSystem I F.obj ⟶ completionQuotientSystem I G.obj where
  app n := quotientMapOfHom_idealPowers I I (n.unop + 1) (n.unop + 1) le_rfl f.hom
  naturality := by
    intro i j g
    have : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple I (i.unop + 1) F.obj).ι) :=
      epi_cokernelπ_submodule (M := F.obj) (idealPowerMultiple I (i.unop + 1) F.obj)
    refine (cancel_epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple I (i.unop + 1) F.obj).ι)).1 ?_
    have hF := completionQuotientSystem_projection_arrow I F.obj g
    have hG := completionQuotientSystem_projection_arrow I G.obj g
    have pi := quotientMapOfHom_idealPowers_π I I (i.unop + 1) (i.unop + 1) le_rfl f.hom
    have pj := quotientMapOfHom_idealPowers_π I I (j.unop + 1) (j.unop + 1) le_rfl f.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ quotientMapOfHom_idealPowers I I (j.unop + 1) (j.unop + 1)
            le_rfl f.hom) hF).trans
        (pj.trans
          ((congrArg (fun k => f.hom ≫ k) hG.symm).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun k => k ≫ (completionQuotientSystem I G.obj).map g)
                  pi.symm).trans
                (Category.assoc _ _ _))))))

/-- Completion of a coherent sheaf along a quasi-coherent ideal, as a coherent adic inverse
system. -/
@[no_expose,
  stacks 0880 "the functor",
  stacks 0EIK "the same completion functor on an open subscheme, at the restricted ideal"]
public noncomputable def completionFunctor (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      Stacks.Coherent.CoherentAdicSystems I where
  obj F := ⟨completionQuotientSystem I F.obj, completionAdicSystem_property I F⟩
  map f := ObjectProperty.homMk (completionAdicMap I f)
  map_id F := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n =>
    quotientMapOfHom_idealPowers_id I (n.unop + 1) F.obj))
  map_comp f g := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n =>
    quotientMapOfHom_idealPowers_comp I (n.unop + 1) f.hom g.hom))

/-- The `n`-th term of the completion is the quotient by `I ^ (n+1)`. -/
@[stacks 0880 "object formula"]
public theorem completionFunctor_obj (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    ((completionFunctor X I).obj F).obj.obj (op n) = idealPowerQuotient I (n + 1) F.obj :=
  completionQuotientSystem_obj I F.obj n

/-- The canonical projection from a coherent sheaf to a term of its completion. -/
public noncomputable def completionProjection (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    F.obj ⟶ ((completionFunctor X I).obj F).obj.obj (op n) :=
  cokernel.π ((idealPowerMultiple I (n + 1) F.obj).ι) ≫
    eqToHom (completionFunctor_obj X I F n).symm

/-- The projections are compatible with the transition maps of the inverse system. -/
@[stacks 0880 "transition maps"]
public theorem completionProjection_transition (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    completionProjection X I F (n + 1) ≫
        ((completionFunctor X I).obj F).obj.map (homOfLE (Nat.le_succ n)).op =
      completionProjection X I F n := by
  simp only [completionProjection]
  exact completionQuotientSystem_projection I F.obj (Nat.le_succ n)

/-- Completion maps are exactly the maps induced on the successive quotients. -/
@[stacks 0880 "morphism maps"]
public theorem completionFunctor_map_quotient (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (f : F ⟶ G) (n : ℕ) :
    completionProjection X I F n ≫ ((completionFunctor X I).map f).hom.app (op n) =
      f.hom ≫ completionProjection X I G n := by
  simp only [completionProjection]
  exact quotientMapOfHom_idealPowers_π I I (n + 1) (n + 1) le_rfl f.hom

end Stacks.Algebraization

end
