module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChartTautological
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.EpiGlue
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.UnitSection
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic

/-!
# The pullback of the twist of a projective bundle along a chart-wise `Proj` morphism

Let `γ : X' ⟶ X` be a morphism of schemes, `ℰ` a module on `X` and `ℰ'` one on `X'` (both with
quasi-coherent symmetric powers), `u : γ^*ℰ ⟶ ℰ'`, and `h : 𝐏(ℰ') ⟶ 𝐏(ℰ)` a morphism of projective
bundles over `γ` which, over the chart of an affine open `U'` of `X'` lying over an affine open
`U` of `X`, is `Proj` of a graded ring map `φ : Γ(U, Sym ℰ) ⟶ Γ(U', Sym ℰ')` sending the degree-one
element of `x ∈ Γ(U, ℰ)` to the degree-one element of `u(γ^*x)|_{U'}`.

On such a chart the pulled-back tautological quotient `π'^*γ^*ℰ ≅ h^*π^*ℰ ⟶ h^*𝒪(1)` factors
the tautological quotient `π'^*γ^*ℰ ⟶ π'^*ℰ' ⟶ 𝒪'(1)`: through the chart identifications of the
twists and the comparison `(Proj φ)^*𝒪(1) ⟶ 𝒪(1)` of Tag 01MY, both send the pullback of `x` to
the global section of `𝒪(1)` attached to the image of `x`, and a morphism out of a pullback of a
quasi-coherent module along a map into an affine open is determined by such values
(`Stacks.Chow.GenuineChern.pullback_hom_ext_of_isAffineOpen`).

## Main definitions

* `Stacks.Chow.GenuineChern.twistQuotientPullback` and `twistQuotientTarget`: the two quotients.
* `Stacks.Chow.GenuineChern.projMapTwist`: the comparison `(Proj φ)^*𝒪(n) ⟶ 𝒪(n)`.

## Main results

* `Stacks.Chow.GenuineChern.exists_chart_factorization`: **the local factorization**, on the
  chart over `U'`.

## Implementation notes

Morphisms whose objects are absolute twisting sheaves are composed only after their types are
ascribed in the category of modules of the scheme (`chartTwistIso`, `projMapTwist`), and the
composite is then passed around as an opaque variable (`exists_chartTwistComparison`): unifying
through it otherwise exhausts the recursion budget.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.SymGraded

universe u

namespace Stacks.Chow.GenuineChern

section Sections

variable {X Y : Scheme.{u}}

/-- Restricting a section to an open that is equal to `⊤`. -/
abbrev resTop (N : X.Modules) {V : X.Opens} (h : ⊤ ≤ V) (s : Γ(N, V)) : Γ(N, ⊤) :=
  N.val.map (homOfLE h).op s

/-- A morphism of modules commutes with restriction of sections to an open equal to `⊤`. -/
theorem app_resTop {N N' : X.Modules} (α : N ⟶ N') {V : X.Opens} (h : ⊤ ≤ V) (s : Γ(N, V)) :
    α.val.app (op ⊤) (resTop N h s) = resTop N' h (α.val.app (op V) s) :=
  PresheafOfModules.naturality_apply α.val (homOfLE h).op s

/-- Restricting a section along `W ≤ Z` and then along `V ≤ W` is restriction along `V ≤ Z`. -/
theorem map_map_homOfLE (N : X.Modules) {V W Z : X.Opens} (h₁ : V ≤ W) (h₂ : W ≤ Z)
    (s : Γ(N, Z)) :
    N.val.map (homOfLE h₁).op (N.val.map (homOfLE h₂).op s) =
      N.val.map (homOfLE (h₁.trans h₂)).op s := by
  change N.presheaf.map (homOfLE h₁).op (N.presheaf.map (homOfLE h₂).op s) =
    N.presheaf.map (homOfLE (h₁.trans h₂)).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting along `V ≤ W` and then to `⊤ ≤ V` is restricting to `⊤ ≤ W`. -/
theorem resTop_map (N : X.Modules) {V W : X.Opens} (h : ⊤ ≤ V) (h' : V ≤ W) (s : Γ(N, W)) :
    resTop N h (N.val.map (homOfLE h').op s) = resTop N (h.trans h') s := by
  change N.presheaf.map (homOfLE h).op (N.presheaf.map (homOfLE h').op s) =
    N.presheaf.map (homOfLE (h.trans h')).op s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The component of a composite of module morphisms, evaluated on a section. -/
theorem comp_app_apply {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (V : X.Opens)
    (x : M.val.obj (op V)) : (f ≫ g).val.app (op V) x = g.val.app (op V) (f.val.app (op V) x) := rfl

/-- Applying a morphism of modules to a restricted section and then restricting to `⊤` agrees
with restricting to `⊤` first and then applying the morphism. -/
theorem resTop_app_map {N N' : X.Modules} (α : N ⟶ N') {V W : X.Opens} (hV : ⊤ ≤ V)
    (k : V ≤ W) (z : Γ(N, W)) :
    resTop N' hV (α.val.app (op V) (N.val.map (homOfLE k).op z)) =
      α.val.app (op ⊤) (resTop N (hV.trans k) z) :=
  (congrArg (resTop N' hV) (PresheafOfModules.naturality_apply α.val (homOfLE k).op z)).trans
    ((resTop_map N' hV k _).trans (app_resTop α (hV.trans k) z).symm)

/-- Restriction of sections to an open equal to `⊤` is injective. -/
theorem resTop_injective (N : X.Modules) {V : X.Opens} (h : ⊤ ≤ V) :
    Function.Injective (resTop N h) := by
  obtain rfl : V = ⊤ := top_le_iff.mp h
  intro a b hab
  have e : ∀ c : Γ(N, ⊤), resTop N h c = c := fun c => by
    change N.val.map (homOfLE h).op c = c
    rw [show homOfLE h = 𝟙 _ from rfl, op_id, PresheafOfModules.map_id]
    rfl
  rwa [e, e] at hab

/-- **Congruence of pulled-back sections, without heterogeneous equality.** -/
theorem pullbackCongr_hom_unitSection_eq {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (U : Y.Opens) (s : Γ(M, U)) (hle : f ⁻¹ᵁ U ≤ g ⁻¹ᵁ U) :
    ((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op (f ⁻¹ᵁ U)) (unitSection f M U s) =
      ((Scheme.Modules.pullback g).obj M).val.map (homOfLE hle).op (unitSection g M U s) := by
  subst hf
  rw [show homOfLE hle = 𝟙 _ from rfl, op_id, PresheafOfModules.map_id]
  rfl

/-- **Restriction to an open immersion, read on pulled-back sections**: the comparison of
`Scheme.Modules.restrictFunctorIsoPullback` carries the pulled-back section to the restriction of
the section. -/
theorem restrictFunctorIsoPullback_inv_unitSection (c : X ⟶ Y) [IsOpenImmersion c]
    (M : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app M).val.app (op (c ⁻¹ᵁ V))
        (unitSection c M V s) =
      M.val.map (homOfLE (c.image_preimage_le V)).op s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction c)
    (Scheme.Modules.pullbackPushforwardAdjunction c) M
  have h' : (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M ≫
      (Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app M) =
      (Scheme.Modules.restrictAdjunction c).unit.app M := by
    rw [← h, Category.assoc, ← Functor.map_comp]
    change _ ≫ (Scheme.Modules.pushforward c).map
      (((Scheme.Modules.restrictFunctorIsoPullback c).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback c).inv).app M) = _
    rw [Iso.hom_inv_id]
    exact (congrArg (fun k => _ ≫ k) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  exact congrArg (fun ρ : M ⟶ (Scheme.Modules.pushforward c).obj
    ((Scheme.Modules.restrictFunctor c).obj M) => ρ.val.app (op V) s) h'

/-- The reverse comparison. -/
theorem restrictFunctorIsoPullback_hom_res (c : X ⟶ Y) [IsOpenImmersion c]
    (M : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback c).hom.app M).val.app (op (c ⁻¹ᵁ V))
        (M.val.map (homOfLE (c.image_preimage_le V)).op s) =
      unitSection c M V s := by
  rw [← restrictFunctorIsoPullback_inv_unitSection]
  exact Stacks.AlgebraicGeometry.PullbackUnit.natIso_hom_inv_app
    (Scheme.Modules.restrictFunctorIsoPullback c) M _ _

/-- The restriction maps of a restriction along an open immersion. -/
theorem restrict_map_apply (c : X ⟶ Y) [IsOpenImmersion c] (M : Y.Modules) {V W : X.Opens}
    (h : V ≤ W) (s : Γ((Scheme.Modules.restrictFunctor c).obj M, W)) :
    ((Scheme.Modules.restrictFunctor c).obj M).val.map (homOfLE h).op s =
      M.val.map (homOfLE (c.image_mono h)).op s := rfl

end Sections



section Square

variable {Z Z' P P' : Scheme.{u}} (c' : Z' ⟶ P') (h : P' ⟶ P) (pm : Z' ⟶ Z) (c : Z ⟶ P)
  [IsOpenImmersion c] (hc : c' ≫ h = pm ≫ c)

/-- For a commutative square `c' ≫ h = pm ≫ c` with `c` an open immersion, the comparison
`c'^*h^*M ≅ (c' ≫ h)^*M = (pm ≫ c)^*M ≅ pm^*c^*M ≅ pm^*(M|_c)`. -/
def squarePullbackRestrict (M : P.Modules) :
    (Scheme.Modules.pullback c').obj ((Scheme.Modules.pullback h).obj M) ⟶
      (Scheme.Modules.pullback pm).obj ((Scheme.Modules.restrictFunctor c).obj M) :=
  (Scheme.Modules.pullbackComp c' h).hom.app M ≫ (Scheme.Modules.pullbackCongr hc).hom.app M ≫
    (Scheme.Modules.pullbackComp pm c).inv.app M ≫
    (Scheme.Modules.pullback pm).map ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app M)

/-- **The square comparison on a twice pulled-back section.** -/
theorem squarePullbackRestrict_unitSection (M : P.Modules) (V : P.Opens) (s : Γ(M, V))
    (h₁ : ⊤ ≤ c' ⁻¹ᵁ (h ⁻¹ᵁ V)) (h₂ : ⊤ ≤ c ⁻¹ᵁ V) :
    (squarePullbackRestrict c' h pm c hc M).val.app (op ⊤)
        (resTop _ h₁ (unitSection c' ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ V)
          (unitSection h M V s))) =
      unitSection pm ((Scheme.Modules.restrictFunctor c).obj M) ⊤
        (resTop _ h₂ (M.val.map (homOfLE (c.image_preimage_le V)).op s)) := by
  have hle : (c' ≫ h) ⁻¹ᵁ V ≤ (pm ≫ c) ⁻¹ᵁ V := by rw [hc]
  have h₁' : ⊤ ≤ (pm ≫ c) ⁻¹ᵁ V := h₁.trans hle
  have e1 : ((Scheme.Modules.pullbackComp c' h).hom.app M).val.app (op ⊤)
      (resTop _ h₁ (unitSection c' ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ V)
        (unitSection h M V s))) = resTop _ h₁ (unitSection (c' ≫ h) M V s) :=
    (app_resTop _ h₁ _).trans (congrArg _ (pullbackComp_hom_unitSection c' h M V s))
  have e2 : ((Scheme.Modules.pullbackCongr hc).hom.app M).val.app (op ⊤)
      (resTop _ h₁ (unitSection (c' ≫ h) M V s)) = resTop _ h₁' (unitSection (pm ≫ c) M V s) :=
    (app_resTop _ h₁ _).trans ((congrArg _ (pullbackCongr_hom_unitSection_eq hc M V s hle)).trans
      (resTop_map _ h₁ hle _))
  have e3 : ((Scheme.Modules.pullbackComp pm c).inv.app M).val.app (op ⊤)
      (resTop _ h₁' (unitSection (pm ≫ c) M V s)) =
        unitSection pm ((Scheme.Modules.pullback c).obj M) ⊤
          (resTop _ h₂ (unitSection c M V s)) :=
    (app_resTop _ h₁' _).trans ((congrArg _ (pullbackComp_inv_unitSection pm c M V s)).trans
      (unitSection_restrict pm ((Scheme.Modules.pullback c).obj M) h₂ _).symm)
  have e4 : ((Scheme.Modules.pullback pm).map
      ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app M)).val.app (op ⊤)
      (unitSection pm ((Scheme.Modules.pullback c).obj M) ⊤
        (resTop _ h₂ (unitSection c M V s))) =
      unitSection pm ((Scheme.Modules.restrictFunctor c).obj M) ⊤
        (resTop _ h₂ (M.val.map (homOfLE (c.image_preimage_le V)).op s)) :=
    (unitSection_pullback_map pm _ ⊤ _).trans (congrArg _ ((app_resTop _ h₂ _).trans
      (congrArg _ (restrictFunctorIsoPullback_inv_unitSection c M V s))))
  exact (congrArg _ (congrArg _ (congrArg _ e1))).trans
    ((congrArg _ (congrArg _ e2)).trans ((congrArg _ e3).trans e4))

end Square

section Theta

variable {S B σ τ : Type u} [CommRing S] [CommRing B] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒮 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒮] [GradedRing ℬ]

open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection in
/-- The comparison `(Proj φ)^*𝒪(n) ⟶ 𝒪(n)` of Tag 01MY for an everywhere defined `φ`, as the
composite whose value on homogeneous global sections is
`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.composite_degreeSection`. -/
def projMapTwist (φ : 𝒮 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map φ) (n : ℤ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).obj (twistingSheafModule 𝒮 n) ⟶
      twistingSheafModule ℬ n :=
  have hdom := Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map 𝒮 ℬ φ hφ
  ((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒮 ℬ φ hφ hdom)).inv.app
        (twistingSheaf 𝒮 n) ≫
      (Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ φ hdom)
        (Stacks.AlgebraicGeometry.ProjTwistChain.mapHom 𝒮 ℬ φ)).inv.app (twistingSheaf 𝒮 n) ≫
      (Scheme.Modules.pullback (baseChange 𝒮 ℬ φ hdom)).map
        (Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap 𝒮 ℬ φ n)) ≫
    ((Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ φ hdom)
        (Stacks.AlgebraicGeometry.ProjShared.mapDomain 𝒮 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
      (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒮 ℬ φ hdom)).hom.app (twistingSheaf ℬ n) ≫
      (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app (twistingSheaf ℬ n))

/-- The comparison `projMapTwist` sends the pullback of the degree-`n` section of `𝒪(n)` attached
to `a` to the degree-`n` section attached to `φ a`. -/
theorem projMapTwist_degreeSection (φ : 𝒮 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map φ) (n : ℕ)
    (a : 𝒮 n) :
    (projMapTwist φ hφ (n : ℤ)).val.app (op ⊤)
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (AlgebraicGeometry.Proj.map φ hφ)
          (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a)) =
      degreeSection ℬ n ⟨φ a, φ.map_mem a.2⟩ :=
  Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.composite_degreeSection φ hφ _ n a

end Theta

section Twist

variable {X X' : Scheme.{u}} (γ : X' ⟶ X) {E : X.Modules} {E' : X'.Modules}
  (hqc : IsQuasicoherentPieces E) (hqc' : IsQuasicoherentPieces E')
  (u : (Scheme.Modules.pullback γ).obj E ⟶ E')
  (h : (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  (hh : h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)

/-- The canonical identification `π'^*γ^*ℰ ≅ h^*π^*ℰ`. -/
def twistPullbackSourceIso :
    (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
        ((Scheme.Modules.pullback γ).obj E) ≅
      (Scheme.Modules.pullback h).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).obj E) :=
  (Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase γ).app E ≪≫
    (Scheme.Modules.pullbackCongr hh.symm).app E ≪≫
    ((Scheme.Modules.pullbackComp h (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).app
      E).symm

/-- The pulled-back tautological quotient `π'^*γ^*ℰ ≅ h^*π^*ℰ ⟶ h^*𝒪(1)`. -/
def twistQuotientPullback :
    (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
        ((Scheme.Modules.pullback γ).obj E) ⟶
      (Scheme.Modules.pullback h).obj (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) :=
  (twistPullbackSourceIso γ hqc hqc' h hh).hom ≫
    (Scheme.Modules.pullback h).map (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)

/-- The tautological quotient of `ℰ'` precomposed with `u`: `π'^*γ^*ℰ ⟶ π'^*ℰ' ⟶ 𝒪'(1)`. -/
def twistQuotientTarget :
    (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
        ((Scheme.Modules.pullback γ).obj E) ⟶
      Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc' :=
  (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).map u ≫
    Stacks.ProjectiveBundleSplitting.tautologicalMap E' hqc'

end Twist


section Values

variable {X X' : Scheme.{u}} (γ : X' ⟶ X) {E : X.Modules} {E' : X'.Modules}
  (hqc : IsQuasicoherentPieces E) (hqc' : IsQuasicoherentPieces E')
  (u : (Scheme.Modules.pullback γ).obj E ⟶ E')
  (h : (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  (hh : h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)

/-- **The pulled-back tautological quotient on a pulled-back section.** -/
theorem twistQuotientPullback_unitSection (U : X.Opens) (x : Γ(E, U))
    (hle : ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U ≤
      (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U) :
    (twistQuotientPullback γ hqc hqc' h hh).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
        (unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          ((Scheme.Modules.pullback γ).obj E) (γ ⁻¹ᵁ U) (unitSection γ E U x)) =
      ((Scheme.Modules.pullback h).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.map (homOfLE hle).op
        (unitSection h (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
          (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))) := by
  have s1 := pullbackComp_hom_unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
    γ E U x
  have s2 := pullbackCongr_hom_unitSection_eq hh.symm E U x hle
  have s3 := pullbackComp_inv_unitSection h (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
    E U x
  have s4 := unitSection_pullback_map h (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (unitSection (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase E U x)
  have s5 := tautologicalMap_unitSection E hqc U x
  refine (congrArg (fun z =>
    ((Scheme.Modules.pullback h).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackComp h
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E).val.app
          (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackCongr hh.symm).hom.app E).val.app
          (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) z)))
    s1).trans ?_
  refine (congrArg (fun z =>
    ((Scheme.Modules.pullback h).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackComp h
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E).val.app
          (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) z))
    s2).trans ?_
  refine (congrArg (fun z =>
    ((Scheme.Modules.pullback h).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) z)
    (PresheafOfModules.naturality_apply ((Scheme.Modules.pullbackComp h
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app E).val
      (homOfLE hle).op _)).trans ?_
  refine (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback h).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val (homOfLE hle).op _).trans ?_
  refine congrArg (((Scheme.Modules.pullback h).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)).val.map (homOfLE hle).op) ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullback h).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc)).val.app
        (op ((h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U)) z) s3).trans ?_
  refine s4.trans ?_
  exact congrArg _ s5

/-- **The tautological quotient of `ℰ'`, precomposed with `u`, on a pulled-back section.** -/
theorem twistQuotientTarget_unitSection (U : X.Opens) (x : Γ(E, U)) :
    (twistQuotientTarget γ hqc' u).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
        (unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          ((Scheme.Modules.pullback γ).obj E) (γ ⁻¹ᵁ U) (unitSection γ E U x)) =
      ((projectiveBundleTwistData E' hqc').ψ 1).val.app (op (γ ⁻¹ᵁ U))
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op (γ ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
            (op U) x)) := by
  have s1 := unitSection_pullback_map (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase u
    (γ ⁻¹ᵁ U) (unitSection γ E U x)
  refine (congrArg (fun z => (Stacks.ProjectiveBundleSplitting.tautologicalMap E' hqc').val.app
      (op ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ (γ ⁻¹ᵁ U))) z) s1).trans ?_
  refine (tautologicalMap_unitSection E' hqc' (γ ⁻¹ᵁ U) _).trans ?_
  have s2 : u.val.app (op (γ ⁻¹ᵁ U)) (unitSection γ E U x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app (op U) x := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [s2]

end Values


section Chart

open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {X X' : Scheme.{u}} {E : X.Modules} {E' : X'.Modules}
  (hqc : IsQuasicoherentPieces E) (hqc' : IsQuasicoherentPieces E')
  (h : (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  {U' : X'.Opens} (hU' : IsAffineOpen U') {U : X.Opens} (hU : IsAffineOpen U)
  (φ : (schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ
    (schemeSheafGradedAlgebra E' hqc').grading U')
  (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E' hqc').grading U') ≤
    (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U)).map φ)
  (hc : (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫ h =
    AlgebraicGeometry.Proj.map φ hφ ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)

/-- The chart identification of the degree-one twist, with its type declared in the category of
modules on the chart, so that it composes there. -/
def chartTwistIso (E : X.Modules) (hqc : IsQuasicoherentPieces E) (U : X.Opens)
    (hU : IsAffineOpen U) :
    (Scheme.Modules.restrictFunctor
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) ≅
      twistingSheafModule ((schemeSheafGradedAlgebra E hqc).grading U) ((1 : ℕ) : ℤ) :=
  (projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)

/-- The components of the forward map of `chartTwistIso`. -/
theorem chartTwistIso_hom_app (E : X.Modules) (hqc : IsQuasicoherentPieces E) (U : X.Opens)
    (hU : IsAffineOpen U) (V) (z) :
    (chartTwistIso E hqc U hU).hom.val.app V z =
      ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).hom.val.app V z :=
  rfl

/-- The components of the inverse map of `chartTwistIso`. -/
theorem chartTwistIso_inv_app (E : X.Modules) (hqc : IsQuasicoherentPieces E) (U : X.Opens)
    (hU : IsAffineOpen U) (V) (z) :
    (chartTwistIso E hqc U hU).inv.val.app V z =
      ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv.val.app V z :=
  rfl

/-- The chart over an affine open `U` of the base covers the preimage of `U` in the projective
bundle. -/
private theorem top_le_chart_preimage_toBase (E : X.Modules) (hqc : IsQuasicoherentPieces E)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) := fun y _ => by
  change (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU y) ∈ U
  rw [Stacks.AlgebraicGeometry.RelativeProjMapDomain.toBase_chart_apply]
  exact (projInclusionToOpen _ U hU y).2

/-- On the chart over `U`, the restricted degree-one value attached to `x` is the inverse chart
identification applied to the degree-one section attached to the degree-one element of `x`. -/
private theorem restrict_twist_psi_eq_chartIso_inv (E : X.Modules) (hqc : IsQuasicoherentPieces E)
    (U : X.Opens) (hU : IsAffineOpen U) (x : Γ(E, U))
    (h₂ : ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)) :
    resTop ((Scheme.Modules.restrictFunctor
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) h₂
      ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
        (homOfLE (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU).image_preimage_le
          _)).op (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))) =
      ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv.val.app
        (op ⊤) (degreeSection ((schemeSheafGradedAlgebra E hqc).grading U) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading U _⟩) :=
  (restrict_map_apply _ _ h₂ _).trans
    ((map_map_homOfLE _ (Scheme.Hom.image_mono _ h₂) (Scheme.Hom.image_preimage_le _ _) _).trans
      (chartIso_inv_degreeSection U hU _
        ((Scheme.Hom.image_mono _ h₂).trans (Scheme.Hom.image_preimage_le _ _))).symm)

/-- **The chart half of the comparison on the restriction of a homogeneous-section value.** -/
theorem chartTwistComparisonAux_spec (x : Γ(E, U)) (x' : Γ(E', U'))
    (hdeg : φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) =
      DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))
    (h₂ : ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
    (h₃ : ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')) :
    ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).map
      (chartTwistIso E hqc U hU).hom ≫
    projMapTwist φ hφ ((1 : ℕ) : ℤ) ≫
    (chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (AlgebraicGeometry.Proj.map φ hφ)
          ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
          (resTop ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) h₂
            ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
              (homOfLE
                (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU).image_preimage_le
                _)).op
              (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
                ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))))) =
      resTop ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) h₃
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')
          (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U')
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))) := by
  have hinv := congrArg (fun ρ => ρ.val.app (op ⊤)
      (degreeSection ((schemeSheafGradedAlgebra E hqc).grading U) 1
          ⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x),
            (schemeSheafGradedAlgebra E hqc).of_mem_grading U _⟩))
    ((projectiveBundleTwistData E hqc).chartData.chartIso U hU ((1 : ℕ) : ℤ)).inv_hom_id
  have hdeg' : (⟨φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)), φ.map_mem
          ((schemeSheafGradedAlgebra E hqc).of_mem_grading U _)⟩ :
        (schemeSheafGradedAlgebra E' hqc').grading U' 1) =
      ⟨DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'),
        (schemeSheafGradedAlgebra E' hqc').of_mem_grading U' _⟩ := Subtype.ext hdeg
  have hy := restrict_twist_psi_eq_chartIso_inv E hqc U hU x h₂
  have hy' := (restrict_twist_psi_eq_chartIso_inv E' hqc' U' hU' x' h₃).symm
  have e1 : ∀ w, ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).map
      (chartTwistIso E hqc U hU).hom ≫
    projMapTwist φ hφ ((1 : ℕ) : ℤ) ≫
    (chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤) w =
    (projMapTwist φ hφ ((1 : ℕ) : ℤ) ≫
    (chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
          (((Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).map
            (chartTwistIso E hqc U hU).hom).val.app (op ⊤) w) := fun w => by
    exact comp_app_apply _ _ _ w
  have e2 : ∀ w, (projMapTwist φ hφ ((1 : ℕ) : ℤ) ≫
    (chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤) w =
    ((chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
          ((projMapTwist φ hφ ((1 : ℕ) : ℤ)).val.app (op ⊤) w) := fun w => by
    exact comp_app_apply _ _ _ w
  have e3 : ∀ w, ((chartTwistIso E' hqc' U' hU').inv ≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤) w =
    ((Scheme.Modules.restrictFunctorIsoPullback
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
          ((chartTwistIso E' hqc' U' hU').inv.val.app (op ⊤) w) := fun w => by
    exact comp_app_apply _ _ _ w
  rw [e1, e2, e3]
  refine Eq.trans (congrArg (fun z =>
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
      ((chartTwistIso E' hqc' U' hU').inv.val.app
        (op ⊤) ((projMapTwist φ hφ ((1 : ℕ) : ℤ)).val.app (op ⊤) z)))
    ((Stacks.AlgebraicGeometry.PullbackUnit.pullback_map_pullbackSection _ _ _).trans
      (congrArg _ ((congrArg _ hy).trans hinv)))) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤)
      ((chartTwistIso E' hqc' U' hU').inv.val.app (op ⊤) z))
    ((projMapTwist_degreeSection φ hφ 1 _).trans (congrArg _ hdeg'))) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Scheme.Modules.restrictFunctorIsoPullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')).val.app (op ⊤) z) hy') ?_
  exact (app_resTop _ h₃ _).trans (congrArg _ (restrictFunctorIsoPullback_hom_res _ _ _ _))

/-- **The chart comparison of the two twists**, as an existence statement with its value on the
restricted homogeneous-section values. -/
theorem exists_chartTwistComparison :
    ∃ Λ : (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).obj
        ((Scheme.Modules.restrictFunctor
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⟶
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc'),
    ∀ (x : Γ(E, U)) (x' : Γ(E', U'))
      (_ : φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) =
      DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))
      (h₂ : ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
      (h₃ : ⊤ ≤ (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ⁻¹ᵁ
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')),
    Λ.val.app (op ⊤)
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (AlgebraicGeometry.Proj.map φ hφ)
          ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
          (resTop ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) h₂
            ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
              (homOfLE
                (((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU).image_preimage_le
                _)).op
              (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
                ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))))) =
      resTop ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) h₃
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')
          (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U')
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))) :=
  ⟨_, fun x x' hdeg h₂ h₃ => chartTwistComparisonAux_spec hqc hqc' hU' hU φ hφ x x' hdeg h₂ h₃⟩

end Chart


section Spec

open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

variable {X X' : Scheme.{u}} (γ : X' ⟶ X) {E : X.Modules} {E' : X'.Modules}
  (hqc : IsQuasicoherentPieces E) (hqc' : IsQuasicoherentPieces E') [E.IsQuasicoherent]
  (u : (Scheme.Modules.pullback γ).obj E ⟶ E')
  (h : (relativeProj (schemeSheafGradedAlgebra E' hqc')).scheme ⟶
    (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme)
  (hh : h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
    (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)
  {U' : X'.Opens} (hU' : IsAffineOpen U') {U : X.Opens} (hU : IsAffineOpen U)
  (hUU' : U' ≤ γ ⁻¹ᵁ U)
  (φ : (schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ
    (schemeSheafGradedAlgebra E' hqc').grading U')
  (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E' hqc').grading U') ≤
    (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U)).map φ)
  (hc : (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫ h =
    AlgebraicGeometry.Proj.map φ hφ ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)
  (hdeg : ∀ x : Γ(E, U),
    φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) =
      DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') (E'.val.map (homOfLE hUU').op
          (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app (op U) x))))


omit [SheafOfModules.IsQuasicoherent E] in
/-- The tautological quotient of `ℰ'`, on the chart over `U'`, at a twice pulled-back section,
restricted to the top open. -/
theorem chartFactorization_rhs (x : Γ(E, U))
    (hT : ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU') ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U'))
    (hT' : ⊤ ≤ (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) :
    resTop ((Scheme.Modules.pullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT'
      (((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
            (twistQuotientTarget γ hqc' u)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
          (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
            ((Scheme.Modules.pullback γ).obj E))
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ γ ⁻¹ᵁ U)
          (unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
            ((Scheme.Modules.pullback γ).obj E) (γ ⁻¹ᵁ U)
            (unitSection γ E U x)))) =
      resTop ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')
          (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U')
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U')
              (E'.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
                  (op U) x))))) := by
  have hB := (unitSection_pullback_map
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
    (twistQuotientTarget γ hqc' u) _ _).trans (congrArg _
      (twistQuotientTarget_unitSection γ hqc' u U x))
  have hψ' := (PresheafOfModules.naturality_apply ((projectiveBundleTwistData E' hqc').ψ 1).val
    (homOfLE hUU').op ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op (γ ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
        (op U) x))).symm.trans
    (congrArg (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U'))
      (PresheafOfModules.naturality_apply (Scheme.Modules.symmetricAlgebraGen X' E').val
        (homOfLE hUU').op
        (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
          (op U) x)).symm)
  refine (congrArg (resTop ((Scheme.Modules.pullback
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT') hB).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => resTop ((Scheme.Modules.pullback
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT
    (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U') z)) hψ')
  refine Eq.trans ?_ (congrArg (resTop ((Scheme.Modules.pullback
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT)
    (unitSection_restrict ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
      (Scheme.Hom.preimage_mono (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase hUU')
      (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op (γ ⁻¹ᵁ U))
        ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op (γ ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction γ).homEquiv E E' u).val.app
            (op U) x))))).symm
  exact (resTop_map _ hT _ _).symm

omit [SheafOfModules.IsQuasicoherent E] in
/-- The pulled-back tautological quotient followed by the chart comparison, on the chart over
`U'`, at a twice pulled-back section, restricted to the top open: it is the homogeneous-section
value at the section `x'` the comparison carries the degree-one element of `x` to. -/
theorem chartFactorization_lhs (x : Γ(E, U)) (x' : Γ(E', U'))
    (Λ : (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).obj
        ((Scheme.Modules.restrictFunctor
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⟶
      ((Scheme.Modules.pullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')))
    (h₂ : ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
    (hT : ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU') ⁻¹ᵁ
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U'))
    (hΛ : Λ.val.app (op ⊤)
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection (AlgebraicGeometry.Proj.map φ hφ)
          ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
          (resTop ((Scheme.Modules.restrictFunctor
            ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) h₂
            ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).val.map
              (homOfLE (Scheme.Hom.image_preimage_le
                ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU) _)).op
              (((projectiveBundleTwistData E hqc).ψ 1).val.app (op U)
                ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x))))) =
      resTop ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')
          (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U')
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))))
    (hT' : ⊤ ≤ (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) :
    resTop ((Scheme.Modules.pullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT'
      (((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
            (twistQuotientPullback γ hqc hqc' h hh) ≫
        (squarePullbackRestrict _ h _ _ hc _ ≫ Λ)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
          (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
            ((Scheme.Modules.pullback γ).obj E))
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ γ ⁻¹ᵁ U)
          (unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
            ((Scheme.Modules.pullback γ).obj E) (γ ⁻¹ᵁ U)
            (unitSection γ E U x)))) =
      resTop ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT
        (unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')
          ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ U')
          (((projectiveBundleTwistData E' hqc').ψ 1).val.app (op U')
            ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U') x'))) := by
  have hle : ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U ≤
      (h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U :=
    (congrArg (fun f => f ⁻¹ᵁ U) hh).ge
  have h1 : ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU') ⁻¹ᵁ
      ((h ≫ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U) :=
    hT'.trans (Scheme.Hom.preimage_mono _ hle)
  have hA := ((unitSection_pullback_map
      ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
      (twistQuotientPullback γ hqc hqc' h hh) _ _).trans
    (congrArg _ (twistQuotientPullback_unitSection γ hqc hqc' h hh U x hle))).trans
      (unitSection_restrict ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU') _
        hle _)
  refine (congrArg (resTop ((Scheme.Modules.pullback
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT')
    (comp_app_apply _ _ _ _)).trans ?_
  refine (congrArg (fun z => resTop ((Scheme.Modules.pullback
    ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc')) hT'
    ((squarePullbackRestrict _ h _ _ hc _ ≫ Λ).val.app
      (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)) z)) hA).trans ?_
  refine (resTop_app_map _ hT' _ _).trans ?_
  refine (comp_app_apply _ _ _ _).trans ?_
  refine (congrArg (Λ.val.app (op ⊤)) (squarePullbackRestrict_unitSection _ h _ _ hc
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
    ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) _ h1 h₂)).trans ?_
  exact hΛ

include hdeg hc in
/-- **The local factorization**: on the chart over `U'`, the pulled-back tautological quotient
factors the tautological quotient of `ℰ'`. -/
theorem exists_chart_factorization :
    ∃ ψ : (Scheme.Modules.pullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
        ((Scheme.Modules.pullback h).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) ⟶
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E' hqc'),
    (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
        (twistQuotientPullback γ hqc hqc' h hh) ≫ ψ =
    (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
        (twistQuotientTarget γ hqc' u) := by
  obtain ⟨Λ, hΛ⟩ := exists_chartTwistComparison hqc hqc' hU' hU φ hφ
  refine ⟨squarePullbackRestrict _ h _ _ hc _ ≫ Λ, ?_⟩
  have hT := top_le_chart_preimage_toBase E' hqc' U' hU'
  have hFU : ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U = ⊤ :=
    top_le_iff.mp (hT.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hUU')))
  have hT' : ⊤ ≤ ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U := hFU.ge
  let κ : (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)).obj E ⟶
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).obj
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
          ((Scheme.Modules.pullback γ).obj E)) :=
    (Scheme.Modules.pullbackComp ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ)).inv.app E ≫
      (Scheme.Modules.pullback ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
        ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          γ).inv.app E)
  have : IsIso κ := by dsimp only [κ]; infer_instance
  have : Epi κ := IsIso.epi_of_iso κ
  refine (cancel_epi κ).1 ?_
  refine pullback_hom_ext_of_isAffineOpen _ hU hFU E fun x => ?_
  have hk : κ.val.app (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U))
      (unitSection _ E U x) =
      unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
        ((Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase).obj
          ((Scheme.Modules.pullback γ).obj E))
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ (γ ⁻¹ᵁ U))
        (unitSection (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          ((Scheme.Modules.pullback γ).obj E) (γ ⁻¹ᵁ U) (unitSection γ E U x)) :=
    (congrArg (((Scheme.Modules.pullback
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')).map
        ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          γ).inv.app E)).val.app
        (op (((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) ⁻¹ᵁ U)))
      (pullbackComp_inv_unitSection ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ≫ γ) E U x)).trans
      ((unitSection_pullback_map ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU')
        ((Scheme.Modules.pullbackComp (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase
          γ).inv.app E) _ _).trans
        (congrArg _ (pullbackComp_inv_unitSection
          (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase γ E U x)))
  refine ((comp_app_apply κ _ _ _).trans (congrArg _ hk)).trans
    (Eq.trans ?_ ((comp_app_apply κ _ _ _).trans (congrArg _ hk)).symm)
  have h₂ := top_le_chart_preimage_toBase E hqc U hU
  exact resTop_injective _ hT' ((chartFactorization_lhs (γ := γ) (hqc := hqc) (hqc' := hqc')
    (h := h) (hh := hh) (hU' := hU') (hU := hU) (φ := φ) (hφ := hφ) (hc := hc) x _ Λ h₂ hT
    (hΛ x _ (hdeg x) h₂ hT) hT').trans
    (chartFactorization_rhs (γ := γ) (hqc' := hqc') (u := u) (hU' := hU') (hUU' := hUU')
      x hT hT').symm)

end Spec

end Stacks.Chow.GenuineChern

end
