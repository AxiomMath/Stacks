module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HomOpComplexStageQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisGlobalSectionsPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RingInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpCocycleAct
public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions

/-!
# `Γ^Gal(ℋom^•_ℤ(-, M))` takes quasi-isomorphisms to quasi-isomorphisms

Let `k` be a field, `K/k` a separable algebraic extension and `Y` a quasi-compact and
quasi-separated `k`-scheme. Global sections over `Y_K` of the restriction of a sheaf on `Y_étale`
are the filtered colimit of its sections over the finite stages `Y_E`, `E ⊆ K` finite
(Stacks 09YQ in degree zero, `Stacks.EtaleCohomology.exists_fieldStageSection_eq` and
`Stacks.EtaleCohomology.exists_fieldStageRes_eq_of_fieldStageSection_eq`). So a morphism of
complexes of sheaves which is a quasi-isomorphism on sections over every stage, elementwise on
cocycles, becomes a quasi-isomorphism after `Γ(Y_K, -|_{Y_K})`, and after
`Γ^Gal = Stacks.EtaleCohomology.galoisGlobalSections`
(`Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_map_of_stages`).

Applied to precomposition `ℋom^•_ℤ(L, M) ⟶ ℋom^•_ℤ(L', M)` with a quasi-isomorphism `L' ⟶ L` of
complexes of sheaves of `Λ`-modules, `n Λ = 0`, and `M` the complex underlying a bounded below
complex `K` of injective sheaves of `ℤ/n`-modules, the stage condition holds by
`Stacks.EtaleCohomology.exists_homOpComplexPrecomp_stage_eq_add_d`: this gives
`Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_homOpComplexPrecomp`. The case used in the
derived Poincaré duality of Tag 03VM is the augmentation `j_! F[0] ⟶ I` of an injective
resolution on a compactification `X̄`
(`Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_homOpComplexPrecomp_injectiveResolution`).

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] fextOrderBot fextIsDirected etale_spectrumMap_fext

/-! ### Quasi-isomorphisms on all finite stages -/

section Stages

variable (R : Type) [Ring R] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K]

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- Morphisms of sheaves commute with the transition maps between stages. -/
lemma fieldStageRes_app {G G' : EtaleModules.{u, 0} R Y.left} (v : G ⟶ G') {i j : FExt k K}
    (h : i ≤ j) (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    (v.hom.app _).hom (fieldStageRes R Y K G h a) =
      fieldStageRes R Y K G' h ((v.hom.app _).hom a) :=
  ConcreteCategory.congr_hom (v.hom.naturality _) a

/-- `F ↦ Γ(Y_K, F|_{Y_K})`, sheaves of `R`-modules on `Y_étale` to `R`-modules. -/
abbrev fieldBaseChangeSections : EtaleModules.{u, 0} R Y.left ⥤ ModuleCat.{u + 1} R :=
  etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K) ⋙
    etaleModuleGlobalSections.{u, 0} R (fieldBaseChange Y K)

variable {R Y K}

/-- The section over the final object of a global section of `G|_{Y_K}`. -/
abbrev fieldBaseChangeRes (G : EtaleModules.{u, 0} R Y.left)
    (z : (fieldBaseChangeSections R Y K).obj G) :
    ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj G).obj.obj
      (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) :=
  ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj Y K)).obj G).ΓRes
    (op (Scheme.Etale.mk (𝟙 (fieldBaseChange Y K)))) z

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [Algebra.IsSeparable k K] in
/-- Restriction of global sections of `G|_{Y_K}` to the final object is bijective. -/
lemma fieldBaseChangeRes_bijective (G : EtaleModules.{u, 0} R Y.left) :
    Function.Bijective (fieldBaseChangeRes (K := K) G) :=
  ΓRes_etaleMkId_bijective R _

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- If a global section `z` of `G|_{Y_K}` restricts to the stage section of `a`, then its image
under a morphism `v : G ⟶ G'` restricts to the stage section of the image of `a` under `v`. -/
lemma fieldBaseChangeRes_map {G G' : EtaleModules.{u, 0} R Y.left} (v : G ⟶ G') {i : FExt k K}
    {z : (fieldBaseChangeSections R Y K).obj G}
    {a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))}
    (hz : fieldBaseChangeRes G z = fieldStageSection R Y K G i a) :
    fieldBaseChangeRes G' (((fieldBaseChangeSections R Y K).map v).hom z) =
      fieldStageSection R Y K G' i ((v.hom.app _).hom a) :=
  ΓRes_map_eq_fieldStageSection R Y K G v hz

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [Algebra.IsSeparable k K] in
/-- `fieldBaseChangeRes` is additive. -/
lemma fieldBaseChangeRes_add (G : EtaleModules.{u, 0} R Y.left)
    (z z' : (fieldBaseChangeSections R Y K).obj G) :
    fieldBaseChangeRes G (z + z') = fieldBaseChangeRes G z + fieldBaseChangeRes G z' :=
  map_add _ _ _

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [Algebra.IsSeparable k K] in
/-- `fieldBaseChangeRes` sends zero to zero. -/
lemma fieldBaseChangeRes_zero (G : EtaleModules.{u, 0} R Y.left) :
    fieldBaseChangeRes (K := K) G 0 = 0 :=
  map_zero _

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] in
/-- A global section over `Y_K` pulled back from a stage section. -/
lemma exists_fieldBaseChangeRes_eq (G : EtaleModules.{u, 0} R Y.left) (i : FExt k K)
    (a : G.obj.obj (op ((fieldStageSystem Y K).obj (op i)))) :
    ∃ z : (fieldBaseChangeSections R Y K).obj G,
      fieldBaseChangeRes G z = fieldStageSection R Y K G i a :=
  (fieldBaseChangeRes_bijective G).2 _

variable {A B : CochainComplex (Sheaf Y.left.smallEtaleTopology (ModuleCat.{max (u + 1) u} R)) ℤ}
  (φ : A ⟶ B)

/-- **A morphism of complexes which is a quasi-isomorphism over every finite stage, elementwise,
induces a quasi-isomorphism on sections over `Y_K`** (sections over `Y_K` are the filtered
colimit of the sections over the stages). -/
theorem quasiIso_fieldBaseChangeSections_map_of_stages
    (hS : ∀ (i : FExt k K) (m : ℤ)
      (y : (B.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((B.d (m + 1) (m + 1 + 1)).hom.app _).hom y = 0 →
        ∃ x : (A.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
          ((A.d (m + 1) (m + 1 + 1)).hom.app _).hom x = 0 ∧
          ∃ z : (B.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
            y = ((φ.f (m + 1)).hom.app _).hom x + ((B.d m (m + 1)).hom.app _).hom z)
    (hI : ∀ (i : FExt k K) (m : ℤ)
      (x : (A.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((A.d (m + 1) (m + 1 + 1)).hom.app _).hom x = 0 →
        ∀ z : (B.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
          ((φ.f (m + 1)).hom.app _).hom x = ((B.d m (m + 1)).hom.app _).hom z →
            ∃ w : (A.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
              x = ((A.d m (m + 1)).hom.app _).hom w) :
    QuasiIso
      (((fieldBaseChangeSections R Y K).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}), quasiIso_iff]
  intro i
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by lia⟩
  let Γ := fieldBaseChangeSections R Y K
  refine HomologicalComplex₂.quasiIsoAt_of_elements _ m ?_ ?_
  · intro y hy
    change (Γ.obj (B.X (m + 1)) : Type (u + 1)) at y
    change ((Γ.map (B.d (m + 1) (m + 1 + 1))).hom y = 0) at hy
    obtain ⟨i, a, ha⟩ := exists_fieldStageSection_eq R Y K (B.X (m + 1)) y
    replace ha : fieldBaseChangeRes (B.X (m + 1)) y = fieldStageSection R Y K _ i a := ha
    have hda : fieldStageSection R Y K (B.X (m + 1 + 1)) i
        (((B.d (m + 1) (m + 1 + 1)).hom.app _).hom a) =
          fieldStageSection R Y K (B.X (m + 1 + 1)) i 0 := by
      rw [← fieldBaseChangeRes_map _ ha, hy, fieldBaseChangeRes_zero, fieldStageSection_zero]
    obtain ⟨j, hij, hj⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq R Y K _ _ _ hda
    have hda' : ((B.d (m + 1) (m + 1 + 1)).hom.app _).hom
        (fieldStageRes R Y K (B.X (m + 1)) hij a) = 0 := by
      rw [fieldStageRes_app, hj, map_zero]
    obtain ⟨x, hx, z, hz⟩ := hS j m _ hda'
    obtain ⟨xK, hxK⟩ := exists_fieldBaseChangeRes_eq (A.X (m + 1)) j x
    obtain ⟨zK, hzK⟩ := exists_fieldBaseChangeRes_eq (B.X m) j z
    refine ⟨xK, ?_, zK, ?_⟩
    · change (Γ.map (A.d (m + 1) (m + 1 + 1))).hom xK = 0
      apply (fieldBaseChangeRes_bijective (K := K) (A.X (m + 1 + 1))).1
      rw [fieldBaseChangeRes_map _ hxK, hx, fieldBaseChangeRes_zero, fieldStageSection_zero]
    · change y = (Γ.map (φ.f (m + 1))).hom xK + (Γ.map (B.d m (m + 1))).hom zK
      apply (fieldBaseChangeRes_bijective (K := K) (B.X (m + 1))).1
      rw [fieldBaseChangeRes_add, fieldBaseChangeRes_map _ hxK, fieldBaseChangeRes_map _ hzK,
        ← fieldStageSection_add, ← hz, ha, fieldStageSection_fieldStageRes]
  · intro x hx z hz
    change (Γ.obj (A.X (m + 1)) : Type (u + 1)) at x
    change (Γ.obj (B.X m) : Type (u + 1)) at z
    change ((Γ.map (A.d (m + 1) (m + 1 + 1))).hom x = 0) at hx
    change (Γ.map (φ.f (m + 1))).hom x = (Γ.map (B.d m (m + 1))).hom z at hz
    obtain ⟨i, -, a, c, ha, hc⟩ := exists_fieldStageSection_eq₂ Y K x z ⊥
    replace ha : fieldBaseChangeRes (A.X (m + 1)) x = fieldStageSection R Y K _ i a := ha
    replace hc : fieldBaseChangeRes (B.X m) z = fieldStageSection R Y K _ i c := hc
    have h1 : fieldStageSection R Y K (A.X (m + 1 + 1)) i
        (((A.d (m + 1) (m + 1 + 1)).hom.app _).hom a) =
          fieldStageSection R Y K (A.X (m + 1 + 1)) i 0 := by
      rw [← fieldBaseChangeRes_map _ ha, hx, fieldBaseChangeRes_zero, fieldStageSection_zero]
    have h2 : fieldStageSection R Y K (B.X (m + 1)) i (((φ.f (m + 1)).hom.app _).hom a) =
        fieldStageSection R Y K (B.X (m + 1)) i (((B.d m (m + 1)).hom.app _).hom c) := by
      rw [← fieldBaseChangeRes_map _ ha, ← fieldBaseChangeRes_map _ hc, hz]
    obtain ⟨j, hij, hj⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq R Y K _ _ _ h1
    obtain ⟨l, hjl, hl⟩ := exists_fieldStageRes_eq_of_fieldStageSection_eq_of_le R Y K _
      hij hij _ _ h2
    have hx' : ((A.d (m + 1) (m + 1 + 1)).hom.app _).hom
        (fieldStageRes R Y K (A.X (m + 1)) (hij.trans hjl) a) = 0 := by
      have := congrArg (fieldStageRes R Y K (A.X (m + 1 + 1)) hjl) hj
      rw [fieldStageRes_fieldStageRes, fieldStageRes_fieldStageRes, map_zero,
        ← fieldStageRes_app] at this
      exact this
    have hz' : ((φ.f (m + 1)).hom.app _).hom
        (fieldStageRes R Y K (A.X (m + 1)) (hij.trans hjl) a) =
          ((B.d m (m + 1)).hom.app _).hom (fieldStageRes R Y K (B.X m) (hij.trans hjl) c) := by
      rw [fieldStageRes_app, fieldStageRes_app]
      exact hl
    obtain ⟨w, hw⟩ := hI l m _ hx' _ hz'
    obtain ⟨wK, hwK⟩ := exists_fieldBaseChangeRes_eq (A.X m) l w
    refine ⟨wK, ?_⟩
    change (Γ.map (A.d m (m + 1))).hom wK = x
    apply (fieldBaseChangeRes_bijective (K := K) (A.X (m + 1))).1
    rw [fieldBaseChangeRes_map _ hwK, ← hw, ha, fieldStageSection_fieldStageRes]

/-- **The same over `Γ^Gal`**: a morphism of complexes which is a quasi-isomorphism over every
finite stage, elementwise, induces a quasi-isomorphism of complexes of discrete Galois modules
after `Γ^Gal = Stacks.EtaleCohomology.galoisGlobalSections`. -/
theorem quasiIso_galoisGlobalSections_map_of_stages
    (hS : ∀ (i : FExt k K) (m : ℤ)
      (y : (B.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((B.d (m + 1) (m + 1 + 1)).hom.app _).hom y = 0 →
        ∃ x : (A.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
          ((A.d (m + 1) (m + 1 + 1)).hom.app _).hom x = 0 ∧
          ∃ z : (B.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
            y = ((φ.f (m + 1)).hom.app _).hom x + ((B.d m (m + 1)).hom.app _).hom z)
    (hI : ∀ (i : FExt k K) (m : ℤ)
      (x : (A.X (m + 1)).obj.obj (op ((fieldStageSystem Y K).obj (op i)))),
      ((A.d (m + 1) (m + 1 + 1)).hom.app _).hom x = 0 →
        ∀ z : (B.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
          ((φ.f (m + 1)).hom.app _).hom x = ((B.d m (m + 1)).hom.app _).hom z →
            ∃ w : (A.X m).obj.obj (op ((fieldStageSystem Y K).obj (op i))),
              x = ((A.d m (m + 1)).hom.app _).hom w) :
    QuasiIso (((galoisGlobalSections R Y K).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have : (Stacks.Injectives.continuousModuleUnderlying R (K ≃ₐ[k] K)).PreservesHomology := by
    have h := (Functor.exact_tfae (Stacks.Injectives.continuousModuleUnderlying R
      (K ≃ₐ[k] K))).out 4 3
    exact h.mp ⟨Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat R _,
      Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat R _⟩
  have := Stacks.ContinuousCohomology.reflectsIsomorphisms_injectivesContinuousModuleUnderlying
    R (K ≃ₐ[k] K)
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (Stacks.Injectives.continuousModuleUnderlying R (K ≃ₐ[k] K))]
  exact quasiIso_fieldBaseChangeSections_map_of_stages φ hS hI

end Stages

/-! ### Precomposition with a quasi-isomorphism on `Γ^Gal(ℋom^•_ℤ(-, M))` -/

section HomOp

open Stacks.AbelianInternalHom

variable (Λ : Type) [Ring Λ] {n : ℕ} (hn : (n : Λ) = 0) {k : Type u} [Field k]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

include hn in
/-- **`Γ^Gal(ℋom^•_ℤ(-, M))` takes quasi-isomorphisms to quasi-isomorphisms**: for `Y`
quasi-compact and quasi-separated over `k`, `n Λ = 0`, `f : L' ⟶ L` a quasi-isomorphism of
complexes of sheaves of `Λ`-modules on `Y_étale` and `M` the complex of abelian sheaves underlying
a bounded below complex `K` of injective sheaves of `ℤ/n`-modules, precomposition with `f` induces
a quasi-isomorphism `Γ^Gal(ℋom^•_ℤ(L, M)) ⟶ Γ^Gal(ℋom^•_ℤ(L', M))` of complexes of discrete
`Λᵐᵒᵖ[Gal]`-modules. -/
theorem quasiIso_galoisGlobalSections_homOpComplexPrecomp (Y : Over (Spec (.of k)))
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    {L L' : CochainComplex (Sheaf Y.left.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ}
    (f : L' ⟶ L) [QuasiIso f]
    (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) Y.left) ℤ) (a : ℤ) [K.IsStrictlyGE a]
    [∀ q, Injective (K.X q)] :
    QuasiIso (((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (homOpComplexPrecomp (M := zmodForgetComplex K) f)) := by
  let ψ : ZMod n →+* Λ := ZMod.castHom (ringChar.dvd hn) Λ
  exact quasiIso_galoisGlobalSections_map_of_stages _
    (fun i m y hy => exists_homOpComplexPrecomp_stage_eq_add_d _ ψ f K a m y hy)
    (fun i m x hx z hz => exists_homOpComplex_stage_eq_d _ ψ f K a m x hx z hz)

include hn in
/-- **The case of an injective resolution of `j_! F` on a compactification** (the comparison
`Γ^Gal(ℋom^•_ℤ(I, M)) ⟶ Γ^Gal(ℋom^•_ℤ(j_! F[0], M))` in the derived Poincaré duality of Tag 03VM):
for a compactification `j : X ⟶ X̄` over `k`, a sheaf `F` of `Λ`-modules on `X_étale`, an injective
resolution `ι : j_! F[0] ⟶ I` on `X̄_étale` and `M` the complex underlying a bounded below
complex `K` of injective sheaves of `ℤ/n`-modules on `X̄_étale`, `n Λ = 0`, precomposition with
`ι` is a quasi-isomorphism after `Γ^Gal` over `X̄_k̄`. -/
theorem quasiIso_galoisGlobalSections_homOpComplexPrecomp_injectiveResolution {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))
    (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) (Over.mk j.toBase).left) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [∀ q, Injective (K.X q)] :
    QuasiIso (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homOpComplexPrecomp (M := zmodForgetComplex K) I.ι)) :=
  quasiIso_galoisGlobalSections_homOpComplexPrecomp Λ hn kbar (Over.mk j.toBase) I.ι K a

include hn in
/-- `Stacks.EtaleCohomology.quasiIso_galoisGlobalSections_homOpComplexPrecomp_injectiveResolution`
for the target `etaleHomOpTarget` of the Galois evaluation pairing: the complex of abelian sheaves
underlying `K` viewed as a complex of sheaves of abelian groups. Its source and target are
`galoisHomOpE (Over.mk j.toBase) kbar I.cocomplex Kc` and
`galoisHomOpE (Over.mk j.toBase) kbar (j_! F[0]) Kc`. -/
theorem quasiIso_galoisHomOpE_precomp_injectiveResolution {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)))
    (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) (Over.mk j.toBase).left) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] [∀ q, Injective (K.X q)] :
    QuasiIso (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
        (((etaleModuleRestrictScalars (Int.castRingHom (ZMod n))
          (Over.mk j.toBase).left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) I.ι)) :=
  quasiIso_galoisGlobalSections_homOpComplexPrecomp_injectiveResolution Λ hn kbar f j F I K a

end HomOp

end Stacks.EtaleCohomology
