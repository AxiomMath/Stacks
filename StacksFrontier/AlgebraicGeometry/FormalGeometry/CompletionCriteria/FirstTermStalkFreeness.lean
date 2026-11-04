module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Module.RingEquivTransport
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactSequences
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenStalkExactness

/-!
# The localization of `M` modulo `f` is free, for `M` realizing `F_1`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`, and let `(F_n)` be a coherent `I`-adic
system on `U` whose terms are finite locally free over the infinitesimal neighbourhoods —
conditions (1) and (2) of Stacks 0DXW, with `I = (f)` principal.

This file reads the local content of condition (2) at the *first* term of the system and
transports it from the sheaf side to the algebra side: for a point `y` of `U` lying over the
prime `𝔭` of `A`, the stalk of `F_1` at `y` modulo the stalk of `I` is a free module over
`𝒪_{U,y}/I_y`, and if `M` is an `A`-module whose associated sheaf restricts on `U` to `F_1`,
then `M_𝔭/f M_𝔭` is free over `A_𝔭/f A_𝔭`.

## Main results

* `Stacks.Algebraization.free_quotient_of_ringEquiv` — freeness of `P/IP` over `R/I` transports
  along a ring isomorphism `R ≃+* R'` together with a semilinear additive isomorphism of
  modules.
* `Stacks.Algebraization.free_stalk_zero_of_isFiniteLocallyFreeAdic` — the stalk of `F_1` at a
  point of `U`, modulo the stalk of `I`, is free over the local ring modulo that ideal.
* `Stacks.Algebraization.exists_addEquiv_localizedModule_stalk_restrict_tilde` — the stalk at
  `y` of the restriction of `M~` to `U` is the localization `M_𝔭`, semilinearly over
  `Stacks.Algebraization.pointStalkRingEquiv`.
* `Stacks.Algebraization.free_localizedModule_of_isFiniteLocallyFreeAdic` — **the conclusion**:
  `M_𝔭/f M_𝔭` is a free `A_𝔭/f A_𝔭`-module.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Transport of freeness over a quotient ring -/

/-- A module carrying a compatible `R ⧸ I`-action is annihilated by `I`. -/
theorem smul_top_eq_bot_of_module_quotient {R : Type*} [CommRing R] (I : Ideal R)
    {Z : Type*} [AddCommGroup Z] [Module R Z] [Module (R ⧸ I) Z] [IsScalarTower R (R ⧸ I) Z] :
    I • (⊤ : Submodule R Z) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.2 fun r hr z _ => ?_) bot_le
  rw [← algebraMap_smul (R ⧸ I) r z, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  exact Submodule.zero_mem _

/-- **Freeness of `Z` over `R ⧸ I` gives freeness of `Z ⧸ I Z`**, for a module `Z` carrying a
compatible `R ⧸ I`-action: the projection is then an isomorphism. -/
theorem free_quotient_smul_top_of_free {R : Type*} [CommRing R] (I : Ideal R)
    {Z : Type*} [AddCommGroup Z] [Module R Z] [Module (R ⧸ I) Z] [IsScalarTower R (R ⧸ I) Z]
    [Module.Free (R ⧸ I) Z] :
    Module.Free (R ⧸ I) (Z ⧸ (I • ⊤ : Submodule R Z)) := by
  let e : (Z ⧸ (I • ⊤ : Submodule R Z)) ≃ₗ[R] Z :=
    Submodule.quotEquivOfEqBot _ (smul_top_eq_bot_of_module_quotient I)
  refine free_of_ringEquiv_of_addEquiv (RingEquiv.refl (R ⧸ I)) e.toAddEquiv fun c m => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hl : e.toAddEquiv ((Ideal.Quotient.mk I r) • m) = r • e.toAddEquiv m := by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    exact e.map_smul r m
  rw [hl, RingEquiv.refl_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

/-- **Freeness of the `I`-quotient transported along a ring isomorphism.** If `ε : R ≃+* R'`
carries `I` to `I'` and `G : P ≃+ L` is semilinear over `ε`, then freeness of `P ⧸ I P` over
`R ⧸ I` gives freeness of `L ⧸ I' L` over `R' ⧸ I'`. -/
theorem free_quotient_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (ε : R ≃+* R')
    {I : Ideal R} {I' : Ideal R'} (hI : I.map (ε : R →+* R') = I')
    {P L : Type*} [AddCommGroup P] [Module R P] [AddCommGroup L] [Module R' L]
    (G : P ≃+ L) (hG : ∀ (r : R) (p : P), G (r • p) = ε r • G p)
    [Module.Free (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P))] :
    Module.Free (R' ⧸ I') (L ⧸ (I' • ⊤ : Submodule R' L)) := by
  let : RingHomInvPair (ε : R →+* R') (ε.symm : R' →+* R) := RingHomInvPair.of_ringEquiv ε
  let : RingHomInvPair (ε.symm : R' →+* R) (ε : R →+* R') := RingHomInvPair.symm _ _
  let Gl : P ≃ₛₗ[(ε : R →+* R')] L :=
    { G with map_smul' := hG }
  have hmap : (I • ⊤ : Submodule R P).map (Gl : P →ₛₗ[(ε : R →+* R')] L)
      = (I' • ⊤ : Submodule R' L) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.smul_le.2 fun r hr p _ => ?_
      rw [Submodule.mem_comap,
        show (Gl : P →ₛₗ[(ε : R →+* R')] L) (r • p) = ε r • Gl p from hG r p]
      exact Submodule.smul_mem_smul (hI ▸ Ideal.mem_map_of_mem _ hr) Submodule.mem_top
    · refine Submodule.smul_le.2 fun r' hr' l _ => ?_
      obtain ⟨r, hr, hre⟩ := Ideal.mem_map_iff_of_surjective (ε : R →+* R') ε.surjective |>.mp
        (hI ▸ hr' : r' ∈ I.map (ε : R →+* R'))
      have hre' : ε r = r' := hre
      refine ⟨r • Gl.symm l, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
      rw [show (Gl : P →ₛₗ[(ε : R →+* R')] L) (r • Gl.symm l) = ε r • Gl (Gl.symm l) from
        hG r (Gl.symm l), Gl.apply_symm_apply, hre']
  let Gq := Submodule.Quotient.equiv (I • ⊤ : Submodule R P) (I' • ⊤ : Submodule R' L) Gl hmap
  let εq : (R ⧸ I) ≃+* (R' ⧸ I') := Ideal.quotientEquiv I I' ε hI.symm
  have hGq : ∀ (c : R ⧸ I) (z : P ⧸ (I • ⊤ : Submodule R P)), Gq (c • z) = εq c • Gq z := by
    intro c z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : Gq (r • z) = ε r • Gq z := Gq.map_smulₛₗ r z
    rw [← Ideal.Quotient.algebraMap_eq I, algebraMap_smul, h1,
      show εq (algebraMap R (R ⧸ I) r) = algebraMap R' (R' ⧸ I') (ε r) from rfl,
      algebraMap_smul]
  refine free_of_ringEquiv_of_addEquiv εq.symm Gq.symm.toAddEquiv fun c' m => ?_
  apply Gq.injective
  show Gq (Gq.symm (c' • m)) = Gq (εq.symm c' • Gq.symm m)
  rw [Gq.apply_symm_apply, hGq, Gq.apply_symm_apply, εq.apply_symm_apply]

/-- **Freeness of the `I`-quotient transported along a linear isomorphism.** -/
theorem free_quotient_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {P L : Type*} [AddCommGroup P] [Module R P] [AddCommGroup L] [Module R L]
    (G : P ≃ₗ[R] L) [Module.Free (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P))] :
    Module.Free (R ⧸ I) (L ⧸ (I • ⊤ : Submodule R L)) :=
  free_quotient_of_ringEquiv (RingEquiv.refl R) (Ideal.map_id I) G.toAddEquiv G.map_smul

/-! ### The stalk of `F_1` modulo the ideal -/

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **The stalk of `F_1` at a point of `U`, modulo the stalk of the ideal, is free** over the
local ring modulo that same ideal. -/
theorem free_stalk_zero_of_isFiniteLocallyFreeAdic
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F) (y : S.U.toScheme) :
    Module.Free (S.U.toScheme.presheaf.stalk y ⧸ IdealSheafData.stalk (idealOnOpen S) y)
      ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 0)) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 0)))))) := by
  by_cases hy : y ∈ (idealOnOpen S).support
  · have hqc : (F.obj.obj (op 1)).IsQuasicoherent := F.property.isQuasicoherent 1
    have h0 := free_stalk_quotient_of_isFiniteLocallyFreeAdic S F hfree 0 hy
    rw [← pow_one (IdealSheafData.stalk (idealOnOpen S) y)]
    have hZq := free_quotient_smul_top_of_free
      (IdealSheafData.stalk (idealOnOpen S) y ^ 1)
      (Z := ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 1)) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ 1 •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 1)))))))
    exact free_quotient_of_linearEquiv _
      ((idealPowerQuotientStalkLinearEquiv (idealOnOpen S) 1 (F.obj.obj (op 1)) y).trans
        ((modulesStalkFunctor S.U.toScheme y).mapIso (C := S.U.toScheme.Modules)
          (F.property.quotientIso 0)).toLinearEquiv)
  · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support (idealOnOpen S) y).mpr hy]
    have hsub : ((⊤ : Ideal (S.U.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
          ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 0))))) = ⊤ :=
      Submodule.top_smul _
    have := Submodule.Quotient.subsingleton_iff.mpr hsub
    infer_instance

/-! ### The stalk of `M~|_U` at `y` as a localization of `M` -/

section Localized

open Stacks.AlgebraicGeometry.OpenStalkExactness AlgebraicGeometry.StructureSheaf

variable (M : ModuleCat.{u} (CommRingCat.of S.A)) (y : S.U.toScheme)

/-- The image of `r ∈ A` in the stalk of `Spec A` at a point is the germ of the global section
it defines. -/
theorem algebraMap_specStalk_eq_germ (r : S.A) :
    algebraMap S.A
        ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk (underlyingPrime S y)) r =
      (S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S.A)).inv.hom r) := by
  have h2 := congrArg (fun t : CommRingCat.of S.A ⟶
      (AlgebraicGeometry.Spec (CommRingCat.of S.A)).presheaf.stalk (underlyingPrime S y) =>
    t.hom r) (AlgebraicGeometry.Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S.A)
      (x := underlyingPrime S y))
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
  exact ((AlgebraicGeometry.StructureSheaf.stalkIso S.A
    (underlyingPrime S y)).commutes r).symm.trans h2

/-- The stalk map of the open immersion carries the image of `r ∈ A` in the stalk of `Spec A` to
its image in the local ring of `U`. -/
theorem stalkMap_algebraMap_specStalk (r : S.A) :
    (S.U.ι.stalkMap y).hom
        (algebraMap S.A
          ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
            (underlyingPrime S y)) r) =
      baseToPointStalk S y r := by
  rw [algebraMap_specStalk_eq_germ]
  rfl

/-- **The stalk at `y` of the restriction of `M~` to `U` is the localization of `M` at the prime
under `y`**, as an additive isomorphism semilinear over the identification of the local ring of
`U` at `y` with that localization.

Both sides are models of the localization of `M` at the prime: the stalk of a restriction is the
stalk of the sheaf at the image point
(`Stacks.AlgebraicGeometry.OpenStalkExactness.restrictStalkInv`), the stalk of `M~` is a
localization of `M` by `AlgebraicGeometry.StructureSheaf.toStalkₗ`, and the local ring of `U` at
`y` is a localization of `A` at that prime by
`Stacks.Algebraization.pointStalkRingEquiv`. The semilinearity is obtained from the
`A`-linearity by `IsLocalizedModule.linearMap_ext`: two `A`-linear maps out of a localization
agree once they agree on the image of `A`. -/
theorem exists_addEquiv_localizedModule_stalk_restrict_tilde :
    ∃ G : ((modulesStalkFunctor S.U.toScheme y).obj
          ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) ≃+
        LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (M : Type u),
      ∀ (r : S.U.toScheme.presheaf.stalk y)
        (w : ((modulesStalkFunctor S.U.toScheme y).obj
          ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u)),
        G (r • w) = pointStalkRingEquiv S y r • G w := by
  let : Algebra S.A ↑(S.U.toScheme.presheaf.stalk y) := (baseToPointStalk S y).toAlgebra
  let : Module S.A ((modulesStalkFunctor S.U.toScheme y).obj
      ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) :=
    Module.compHom _ (algebraMap S.A ↑(S.U.toScheme.presheaf.stalk y))
  have htower : IsScalarTower S.A ↑(S.U.toScheme.presheaf.stalk y)
      ((modulesStalkFunctor S.U.toScheme y).obj
        ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hlocR : IsLocalization (underlyingPrime S y).asIdeal.primeCompl
      ↑(S.U.toScheme.presheaf.stalk y) := by
    refine (IsLocalization.isLocalization_iff_of_algEquiv _
      (AlgEquiv.ofRingEquiv (f := (pointStalkRingEquiv S y).symm) ?_)).mp inferInstance
    intro r
    exact (RingEquiv.symm_apply_eq _).mpr (pointStalkRingEquiv_baseToPointStalk_apply S y r).symm
  have hiso := isIso_restrictStalkInv S.U.ι (AlgebraicGeometry.tilde M) y
  have hbij := ConcreteCategory.bijective_of_isIso
    (restrictStalkInv S.U.ι (AlgebraicGeometry.tilde M) y)
  let G₁add : ↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
          (underlyingPrime S y)) ≃+
      ((modulesStalkFunctor S.U.toScheme y).obj
        ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) :=
    AddEquiv.ofBijective _ hbij
  have hsmul : ∀ (r : S.A) (n : ↑(TopCat.Presheaf.stalk
      (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
        (underlyingPrime S y))), G₁add (r • n) = r • G₁add n := by
    intro r n
    have h1 : G₁add (r • n) = G₁add (algebraMap S.A
        ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
          (underlyingPrime S y)) r • n) := by
      rw [IsScalarTower.algebraMap_smul]
    have h2 : G₁add (algebraMap S.A
          ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
            (underlyingPrime S y)) r • n)
        = baseToPointStalk S y r • G₁add n := by
      have h3 := restrictStalkInv_smul S.U.ι (AlgebraicGeometry.tilde M) y
        (algebraMap S.A
          ↑((AlgebraicGeometry.structurePresheafInCommRingCat S.A).stalk
            (underlyingPrime S y)) r) n
      rw [stalkMap_algebraMap_specStalk] at h3
      exact h3
    exact (h1.trans h2).trans rfl
  let G₁ : ↑(TopCat.Presheaf.stalk
        (AlgebraicGeometry.moduleStructurePresheaf S.A (M : Type u)).presheaf
          (underlyingPrime S y)) ≃ₗ[S.A]
      ((modulesStalkFunctor S.U.toScheme y).obj
        ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) :=
    { G₁add.toEquiv with map_add' := G₁add.map_add, map_smul' := hsmul }
  have := IsLocalizedModule.of_linearEquiv (underlyingPrime S y).asIdeal.primeCompl
    (AlgebraicGeometry.StructureSheaf.toStalkₗ S.A (M : Type u) (underlyingPrime S y)) G₁
  let g := IsLocalizedModule.linearEquiv (underlyingPrime S y).asIdeal.primeCompl
    (G₁.toLinearMap ∘ₗ
      AlgebraicGeometry.StructureSheaf.toStalkₗ S.A (M : Type u) (underlyingPrime S y))
    (LocalizedModule.mkLinearMap (underlyingPrime S y).asIdeal.primeCompl (M : Type u))
  have hcompat : ∀ (a : ↑(S.U.toScheme.presheaf.stalk y))
      (w : ((modulesStalkFunctor S.U.toScheme y).obj
        ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u)),
      g (a • w) = (IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
        ↑(S.U.toScheme.presheaf.stalk y)
        (Localization.AtPrime (underlyingPrime S y).asIdeal)) a • g w := by
    intro a w
    have key : (g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton
          ↑(S.U.toScheme.presheaf.stalk y) _ w).restrictScalars S.A)
        = ((LinearMap.toSpanSingleton (Localization.AtPrime (underlyingPrime S y).asIdeal)
            (LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (M : Type u))
            (g w)).restrictScalars S.A) ∘ₗ
          (IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
            ↑(S.U.toScheme.presheaf.stalk y)
            (Localization.AtPrime (underlyingPrime S y).asIdeal)).toLinearEquiv.toLinearMap := by
      refine IsLocalizedModule.linearMap_ext (underlyingPrime S y).asIdeal.primeCompl
        (Algebra.linearMap S.A ↑(S.U.toScheme.presheaf.stalk y))
        (LocalizedModule.mkLinearMap (underlyingPrime S y).asIdeal.primeCompl (M : Type u)) ?_
      ext
      simp [LinearMap.toSpanSingleton, Algebra.linearMap]
    exact LinearMap.congr_fun key a
  have hring : ∀ a : ↑(S.U.toScheme.presheaf.stalk y),
      (IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
        ↑(S.U.toScheme.presheaf.stalk y)
        (Localization.AtPrime (underlyingPrime S y).asIdeal)) a = pointStalkRingEquiv S y a := by
    have h : ((IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
          ↑(S.U.toScheme.presheaf.stalk y)
          (Localization.AtPrime (underlyingPrime S y).asIdeal)).toRingEquiv :
            ↑(S.U.toScheme.presheaf.stalk y) →+*
              Localization.AtPrime (underlyingPrime S y).asIdeal)
        = ((pointStalkRingEquiv S y) : ↑(S.U.toScheme.presheaf.stalk y) →+*
            Localization.AtPrime (underlyingPrime S y).asIdeal) := by
      refine IsLocalization.ringHom_ext (underlyingPrime S y).asIdeal.primeCompl ?_
      ext r
      exact ((IsLocalization.algEquiv (underlyingPrime S y).asIdeal.primeCompl
        ↑(S.U.toScheme.presheaf.stalk y)
        (Localization.AtPrime (underlyingPrime S y).asIdeal)).commutes r).trans
        (pointStalkRingEquiv_baseToPointStalk_apply S y r).symm
    exact fun a => DFunLike.congr_fun h a
  exact ⟨g.toAddEquiv, fun r w => (hcompat r w).trans (congrArg (fun t => t • g w) (hring r))⟩


end Localized

/-! ### The localization of `M` modulo `f` is free -/

/-- **The localization of `M` at a point of `U`, modulo `f`, is free over the local ring modulo
`f`.** Here `M` is an `A`-module whose associated sheaf restricts on `U` to the first term `F_1`
of a coherent `I`-adic system whose terms are finite locally free over the infinitesimal
neighbourhoods, and `I = (f)`.

Freeness holds at the stalk of `F_1` by
`Stacks.Algebraization.free_stalk_zero_of_isFiniteLocallyFreeAdic`; `e` carries it to the stalk
of `M~|_U`, and
`Stacks.Algebraization.exists_addEquiv_localizedModule_stalk_restrict_tilde` together with
`Stacks.Algebraization.free_quotient_of_ringEquiv` transports it to the localization of `M`. -/
theorem free_localizedModule_of_isFiniteLocallyFreeAdic (f : S.A) (hIf : S.I = Ideal.span {f})
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F) (M : ModuleCat.{u} (CommRingCat.of S.A))
    (e : (AlgebraicGeometry.tilde M).restrict S.U.ι ≅ systemObj S F 0) (y : S.U.toScheme) :
    Module.Free
      (Localization.AtPrime (underlyingPrime S y).asIdeal ⧸
        Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f})
      (LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (M : Type u) ⧸
        (Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f} •
          (⊤ : Submodule (Localization.AtPrime (underlyingPrime S y).asIdeal)
            (LocalizedModule (underlyingPrime S y).asIdeal.primeCompl (M : Type u))))) := by
  obtain ⟨G, hG⟩ := exists_addEquiv_localizedModule_stalk_restrict_tilde S M y
  have h1 := free_stalk_zero_of_isFiniteLocallyFreeAdic S F hfree y
  have h2 : Module.Free
      (S.U.toScheme.presheaf.stalk y ⧸ IdealSheafData.stalk (idealOnOpen S) y)
      (((modulesStalkFunctor S.U.toScheme y).obj
          ((AlgebraicGeometry.tilde M).restrict S.U.ι) : Type u) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj
              ((AlgebraicGeometry.tilde M).restrict S.U.ι))))) :=
    free_quotient_of_linearEquiv _
      ((modulesStalkFunctor S.U.toScheme y).mapIso (C := S.U.toScheme.Modules)
        e).toLinearEquiv.symm
  have hmap : Ideal.map ((pointStalkRingEquiv S y) : S.U.toScheme.presheaf.stalk y →+*
        Localization.AtPrime (underlyingPrime S y).asIdeal)
      (IdealSheafData.stalk (idealOnOpen S) y)
      = Ideal.span {algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f} := by
    rw [stalk_idealOnOpen_eq_span_of_ideal_eq_span S f hIf, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) (pointStalkRingEquiv_baseToPointStalk_apply S y f)
  exact free_quotient_of_ringEquiv (pointStalkRingEquiv S y) hmap G hG

end Stacks.Algebraization

end
