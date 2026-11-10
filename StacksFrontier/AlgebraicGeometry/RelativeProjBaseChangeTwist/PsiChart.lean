module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BasePsi
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.PulledTwists
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaData
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.RingedSite

/-!
# The homogeneous-section map of the pulled-back twists, on the charts

For a morphism `h` and a sheaf of graded algebras `G`, the chart identification of `h^*G` built
in `PulledTwists` carries the base change of a homogeneous-section map `ψ₀ : M ⟶ p_* G_n` to a
given value on every section over an affine open `V`, as soon as it does so on the pulled-back
sections from an affine open below and a second datum with the same values exists. The products
are treated in the same way. The concrete applications are in `BasisData`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pullback_hom_app_eq_of_pullbackSection`:
  two morphisms out of the inverse image of a quasi-coherent module agree over an affine open as
  soon as they agree on the pulled-back sections.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.genChartIso_field`.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.genChartIso_field_mul`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u w w'

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Two generic inputs -/

section Generic

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {R₁ R₂ : Type u} {σ : Type w} {τ : Type w'} [CommRing R₁] [CommRing R₂]
  [SetLike σ R₁] [AddSubgroupClass σ R₁] [SetLike τ R₂] [AddSubgroupClass τ R₂]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Tag 01MY, part (1), on pulled-back sections**: the comparison map carries the pullback
along `r_φ` of the homogeneous section of `a` to the pullback along the inclusion of `U(φ)` of the
homogeneous section of `φ a`. -/
theorem twistMap_pullbackSection_top (φ : 𝒜 →+*ᵍ ℬ) (k : ℕ) (a : 𝒜 k) :
    (twistMap 𝒜 ℬ φ (k : ℤ)).val.app (op ⊤)
        (pullbackSection (mapHom 𝒜 ℬ φ) (twistingSheaf 𝒜 (k : ℤ)) ⊤ ⊤ (fun _ _ => trivial)
          (degreeSection 𝒜 k a)) =
      pullbackSection (mapDomain 𝒜 ℬ φ).ι (twistingSheaf ℬ (k : ℤ)) ⊤ ⊤ (fun _ _ => trivial)
        (degreeSection ℬ k ⟨φ a, φ.map_mem a.2⟩) := by
  refine Eq.trans (congrArg _ (Scheme.Modules.pullbackSection_top (mapHom 𝒜 ℬ φ)
    (twistingSheaf 𝒜 (k : ℤ)) (fun _ _ => trivial) (degreeSection 𝒜 k a))) ?_
  refine Eq.trans (ProjTwistTheta.twistMap_degreeSection 𝒜 ℬ φ k a) ?_
  exact (Scheme.Modules.pullbackSection_top (mapDomain 𝒜 ℬ φ).ι (twistingSheaf ℬ (k : ℤ))
    (fun _ _ => trivial) (degreeSection ℬ k ⟨φ a, φ.map_mem a.2⟩)).symm

/-- The restriction maps of a twisting sheaf, read in the category of modules of `Proj`. -/
theorem twistingSheaf_val_map_modules (n : ℤ) {U V : (AlgebraicGeometry.Proj 𝒜).Opens}
    (f : U ⟶ V) (x : (twistingSheaf 𝒜 n).val.obj (op V)) :
    (@id (AlgebraicGeometry.Proj 𝒜).Modules (twistingSheaf 𝒜 n)).val.map f.op x =
      (twistingSheaf 𝒜 n).val.map f.op x :=
  rfl

end Generic

section GenericRestrict

variable {W Z Y : Scheme.{u}} (k : W ⟶ Z) [IsOpenImmersion k] (h : Z ⟶ Y)

/-- Along an open immersion, the identification of restriction with inverse image carries a
pulled-back section over the image of an open to the section pulled back twice. -/
theorem restrictFunctorIsoPullback_hom_pullbackSection (O : Y.Modules) (U1 : Y.Opens)
    (Wo : W.Opens) (hk : k ''ᵁ Wo ≤ h ⁻¹ᵁ U1) (hk' : Wo ≤ k ⁻¹ᵁ (h ⁻¹ᵁ U1))
    (t : O.val.obj (op U1)) :
    ((Scheme.Modules.restrictFunctorIsoPullback k).hom.app
        ((Scheme.Modules.pullback h).obj O)).val.app (op Wo)
        (pullbackSection h O U1 (k ''ᵁ Wo) hk t) =
      pullbackSection k ((Scheme.Modules.pullback h).obj O) (h ⁻¹ᵁ U1) Wo hk'
        (pullbackSection h O U1 (h ⁻¹ᵁ U1) le_rfl t) := by
  have h1 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection k
    ((Scheme.Modules.pullback h).obj O) (h ⁻¹ᵁ U1) Wo hk' hk
    (pullbackSection h O U1 (h ⁻¹ᵁ U1) le_rfl t)
  have h2 := ModuleLimits.pullbackSection_shrink h O U1 (h ⁻¹ᵁ U1) (k ''ᵁ Wo) le_rfl hk hk t
  refine Eq.trans (congrArg _ (h1.trans h2).symm) ?_
  exact TwistRigidity.iso_hom_app_inv_app
    ((Scheme.Modules.restrictFunctorIsoPullback k).app ((Scheme.Modules.pullback h).obj O))
    (op Wo) _

end GenericRestrict

section GenericChart

variable {Y Z W D Vv : Scheme.{u}}
  (G : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
  (h : Z ⟶ Y)
  (k : W ⟶ Z) [IsOpenImmersion k] (ρ : W ⟶ D) (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W)
  (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
  (N : ℤ → Vv.Modules) (Bt : ℤ → W.Modules)
  (χ : ∀ n, (Scheme.Modules.pullback c).obj (G.piece n) ≅ N n)
  (tw : ∀ n, (Scheme.Modules.pullback hU).obj (N n) ⟶ (Scheme.Modules.pullback ι).obj (Bt n))
  (htwIso : ∀ n, IsIso (tw n))

/-- The chart identification of `h^*G` on a pulled-back section, from the values of `χ` and
`tw` on it. -/
theorem genChartIso_hom_pullbackSection (n : ℤ) (U1 : Y.Opens) (t : (G.piece n).val.obj (op U1))
    (d : (N n).val.obj (op ⊤)) (b : (Bt n).val.obj (op ⊤))
    (hχ : (χ n).hom.val.app (op (c ⁻¹ᵁ U1))
        (pullbackSection c (G.piece n) U1 (c ⁻¹ᵁ U1) le_rfl t) =
      (N n).val.map (homOfLE le_top).op d)
    (htw : (tw n).val.app (op ⊤) (pullbackSection hU (N n) ⊤ ⊤ (fun _ _ => trivial) d) =
      pullbackSection ι (Bt n) ⊤ ⊤ (fun _ _ => trivial) b)
    (Wo : W.Opens) (hk : k ''ᵁ Wo ≤ h ⁻¹ᵁ U1) (hk' : Wo ≤ k ⁻¹ᵁ (h ⁻¹ᵁ U1)) :
    (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n).hom.val.app (op Wo)
        (pullbackSection h (G.piece n) U1 (k ''ᵁ Wo) hk t) =
      (Bt n).val.map (homOfLE le_top).op b := by
  rw [genChartIso_hom]
  exact (congrArg ((legTail k h ρ hU c ι e hρι (χ n) (tw n)).val.app (op Wo))
    (restrictFunctorIsoPullback_hom_pullbackSection k h (G.piece n) U1 Wo hk hk' t)).trans
    (legTail_pullbackSection k h ρ hU c ι e hρι (χ n) (tw n) U1 t d b hχ htw Wo hk')

/-- The chart identification of `h^*G` on the base change of a homogeneous-section map, on a
pulled-back section. -/
theorem genChartIso_hom_basePsi {S S' : Scheme.{u}} (p : Y ⟶ S) (p' : Z ⟶ S') (gb : S' ⟶ S)
    (hfg : h ≫ p = p' ≫ gb) {M : S.Modules} (n : ℤ)
    (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj (G.piece n)) (U : S.Opens) (V : S'.Opens)
    (hV : V ≤ gb ⁻¹ᵁ U) (h' : p' ⁻¹ᵁ V ≤ h ⁻¹ᵁ (p ⁻¹ᵁ U)) (a : M.val.obj (op U))
    (d : (N n).val.obj (op ⊤)) (b : (Bt n).val.obj (op ⊤))
    (hχ : (χ n).hom.val.app (op (c ⁻¹ᵁ (p ⁻¹ᵁ U)))
        (pullbackSection c (G.piece n) (p ⁻¹ᵁ U) (c ⁻¹ᵁ (p ⁻¹ᵁ U)) le_rfl
          (ψ₀.val.app (op U) a)) =
      (N n).val.map (homOfLE le_top).op d)
    (htw : (tw n).val.app (op ⊤) (pullbackSection hU (N n) ⊤ ⊤ (fun _ _ => trivial) d) =
      pullbackSection ι (Bt n) ⊤ ⊤ (fun _ _ => trivial) b)
    (Wo : W.Opens) (hWo : k ''ᵁ Wo ≤ p' ⁻¹ᵁ V) (hk' : Wo ≤ k ⁻¹ᵁ (h ⁻¹ᵁ (p ⁻¹ᵁ U))) :
    (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n).hom.val.app (op Wo)
        (((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).piece n).val.map
          (homOfLE hWo).op
          ((basePsi p p' gb h hfg ψ₀).val.app (op V) (pullbackSection gb M U V hV a))) =
      (Bt n).val.map (homOfLE le_top).op b := by
  have h1 := basePsi_pullbackSection p p' gb h hfg ψ₀ U V hV h' a
  have h2 := ModuleLimits.pullbackSection_shrink h (G.piece n) (p ⁻¹ᵁ U) _ _ h' hWo
    (hWo.trans h') (ψ₀.val.app (op U) a)
  have h3 := genChartIso_hom_pullbackSection G h k ρ hU c ι e hρι N Bt χ tw htwIso n (p ⁻¹ᵁ U)
    (ψ₀.val.app (op U) a) d b hχ htw Wo (hWo.trans h') hk'
  exact (congrArg ((genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n).hom.val.app (op Wo))
    ((congrArg (((Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G).piece n).val.map
      (homOfLE hWo).op) h1).trans h2)).trans h3

end GenericChart

section GenericExt

/-- **Two morphisms out of the inverse image of a quasi-coherent module agree over an affine
open** as soon as they agree on the pulled-back sections of an affine open below. -/
theorem pullback_hom_app_eq_of_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) {N : Y.Modules} (φ₁ φ₂ : (Scheme.Modules.pullback f).obj F ⟶ N)
    (h : ∀ a, φ₁.val.app (op V) (pullbackSection f F U V hVU a) =
      φ₂.val.app (op V) (pullbackSection f F U V hVU a))
    (x : ((Scheme.Modules.pullback f).obj F).val.obj (op V)) :
    φ₁.val.app (op V) x = φ₂.val.app (op V) x := by
  have H : (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫
      ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ₁ V) =
      (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫
      ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ₂ V) := by
    refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun a => ?_
    have h1 := affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a
    exact (congrArg (fun z => Scheme.Modules.sectionsLinearMap φ₁ V z) h1).trans
      ((h a).trans (congrArg (fun z => Scheme.Modules.sectionsLinearMap φ₂ V z) h1).symm)
  have e1 : ∀ φ : (Scheme.Modules.pullback f).obj F ⟶ N,
      ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫
        ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap φ V))
        ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).inv x) = φ.val.app (op V) x := by
    intro φ
    have h3 : (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).inv x) = x :=
      Iso.inv_hom_id_apply (affinePullbackSectionsBaseChangeIso f F hU hV hVU) x
    rw [ConcreteCategory.comp_apply, h3]
    rfl
  exact (e1 φ₁).symm.trans ((congrArg (fun q => q
    ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).inv x)) H).trans (e1 φ₂))

end GenericExt

section GenericPsiHom

variable {S' P X : Scheme.{u}} (p : P ⟶ S') (c : X ⟶ P) [IsOpenImmersion c] {M : S'.Modules}
  {Bk : SheafOfModules.{u} (Stacks.CategoryTheory.RingedSite.ofScheme P).ringSheaf}
  {T : X.Modules}

/-- A morphism into the direct image of a sheaf of modules, read through the identification of
the restriction along an open immersion: the morphism into the direct image of the identified
sheaf. -/
def chartPsiHom (ψ : M ⟶ (Scheme.Modules.pushforward p).obj Bk)
    (χ : Scheme.Modules.restrict Bk c ≅ T) :
    M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward c).obj T) :=
  ψ ≫ (Scheme.Modules.pushforward p).map
    ((Scheme.Modules.restrictAdjunction c).unit.app Bk ≫ (Scheme.Modules.pushforward c).map χ.hom)

/-- On sections over `V`, `chartPsiHom p c ψ χ` sends `a` to the image under `χ` of the
restriction of `ψ a` to `c ⁻¹ᵁ (p ⁻¹ᵁ V)`. -/
theorem chartPsiHom_app (ψ : M ⟶ (Scheme.Modules.pushforward p).obj Bk)
    (χ : Scheme.Modules.restrict Bk c ≅ T) (V : S'.Opens) (a : M.val.obj (op V)) :
    (chartPsiHom p c ψ χ).val.app (op V) a =
      χ.hom.val.app (op (c ⁻¹ᵁ (p ⁻¹ᵁ V)))
        (Bk.val.map (homOfLE (c.image_preimage_le (p ⁻¹ᵁ V))).op (ψ.val.app (op V) a)) :=
  rfl

end GenericPsiHom

section GenericField

/-- The inverse image of a sheaf of graded algebras, typed as a graded algebra on the ringed
site of the scheme. -/
abbrev pbAlgS {Y Z : Scheme.{u}} (h : Z ⟶ Y)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) :
    RelativeProjTwists.SchemeGradedAlgebra Z :=
  Stacks.RingedSpace.pullbackGradedAlgebra h.toLRSHom.toShHom G

variable {Y Z W D Vv : Scheme.{u}}
  (G : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
  (h : Z ⟶ Y)
  (k : W ⟶ Z) [IsOpenImmersion k] (ρ : W ⟶ D) (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ W)
  (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 W)
  (N : ℤ → Vv.Modules) (Bt : ℤ → W.Modules)
  (χ : ∀ n, (Scheme.Modules.pullback c).obj (G.piece n) ≅ N n)
  (tw : ∀ n, (Scheme.Modules.pullback hU).obj (N n) ⟶ (Scheme.Modules.pullback ι).obj (Bt n))
  (htwIso : ∀ n, IsIso (tw n))

/-- **The chart identification of `h^*G` on the base change of a homogeneous-section map, on all
sections over an affine open**, from its values on the pulled-back sections and a second datum
with the same values. -/
theorem genChartIso_field_aux {S S' : Scheme.{u}} (p : Y ⟶ S) (p' : Z ⟶ S') (gb : S' ⟶ S)
    (hfg : h ≫ p = p' ≫ gb) {M : S.Modules} [M.IsQuasicoherent] (n : ℤ)
    (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj (G.piece n)) (U : S.Opens)
    (hUa : IsAffineOpen U) (V : S'.Opens) (hVa : IsAffineOpen V) (hV : V ≤ gb ⁻¹ᵁ U)
    (h' : p' ⁻¹ᵁ V ≤ h ⁻¹ᵁ (p ⁻¹ᵁ U))
    (Alg₂ : RelativeProjTwists.SchemeGradedAlgebra Z)
    (χ₂ : Scheme.Modules.restrict (Alg₂.piece n) k ≅ Bt n)
    (ψ₂ : (Scheme.Modules.pullback gb).obj M ⟶ (Scheme.Modules.pushforward p').obj (Alg₂.piece n))
    (R : ((Scheme.Modules.pullback gb).obj M).val.obj (op V) →
      (Bt n).val.obj (op (k ⁻¹ᵁ (p' ⁻¹ᵁ V))))
    (h₂ : ∀ a, χ₂.hom.val.app (op (k ⁻¹ᵁ (p' ⁻¹ᵁ V)))
        ((Alg₂.piece n).val.map (homOfLE (k.image_preimage_le (p' ⁻¹ᵁ V))).op
          (ψ₂.val.app (op V) a)) = R a)
    (dχ : M.val.obj (op U) → (N n).val.obj (op ⊤)) (db : M.val.obj (op U) → (Bt n).val.obj (op ⊤))
    (hχ : ∀ a0, (χ n).hom.val.app (op (c ⁻¹ᵁ (p ⁻¹ᵁ U)))
        (pullbackSection c (G.piece n) (p ⁻¹ᵁ U) (c ⁻¹ᵁ (p ⁻¹ᵁ U)) le_rfl
          (ψ₀.val.app (op U) a0)) =
      (N n).val.map (homOfLE le_top).op (dχ a0))
    (htw : ∀ a0, (tw n).val.app (op ⊤)
        (pullbackSection hU (N n) ⊤ ⊤ (fun _ _ => trivial) (dχ a0)) =
      pullbackSection ι (Bt n) ⊤ ⊤ (fun _ _ => trivial) (db a0))
    (hb : ∀ a0, (Bt n).val.map (homOfLE le_top).op (db a0) = R (pullbackSection gb M U V hV a0))
    (a : ((Scheme.Modules.pullback gb).obj M).val.obj (op V)) :
    (chartPsiHom p' k (Bk := (pbAlgS h G).piece n) (basePsi p p' gb h hfg ψ₀)
        (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n)).val.app (op V) a = R a := by
  have hk' : k ⁻¹ᵁ (p' ⁻¹ᵁ V) ≤ k ⁻¹ᵁ (h ⁻¹ᵁ (p ⁻¹ᵁ U)) := fun _ hx => h' hx
  have key := pullback_hom_app_eq_of_pullbackSection gb M hUa hVa hV
    (chartPsiHom p' k (Bk := (pbAlgS h G).piece n) (basePsi p p' gb h hfg ψ₀)
      (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n))
    (chartPsiHom p' k ψ₂ χ₂) (fun a0 => ?_) a
  · exact key.trans ((chartPsiHom_app p' k ψ₂ χ₂ V a).trans (h₂ a))
  · refine ((chartPsiHom_app p' k (Bk := (pbAlgS h G).piece n) (basePsi p p' gb h hfg ψ₀)
      (genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n) V _).trans ?_).trans
      (chartPsiHom_app p' k ψ₂ χ₂ V _).symm
    have X := genChartIso_hom_basePsi G h k ρ hU c ι e hρι N Bt χ tw htwIso p p' gb hfg
      n ψ₀ U V hV h' a0 (dχ a0) (db a0) (hχ a0) (htw a0) (k ⁻¹ᵁ (p' ⁻¹ᵁ V))
      (k.image_preimage_le (p' ⁻¹ᵁ V)) hk'
    have Y := h₂ (pullbackSection gb M U V hV a0)
    have Z2 := (X.trans (hb a0)).trans Y.symm
    generalize genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n = C at Z2 ⊢
    generalize basePsi p p' gb h hfg ψ₀ = P at Z2 ⊢
    exact Z2

/-- The form of `genChartIso_field_aux` in which the pulled-back module, the chart
identification, the homogeneous-section map and the pulled-back sections are given up to
equality, so that it applies to data that are equal to these but not syntactically so. -/
theorem genChartIso_field {S S' : Scheme.{u}} (p : Y ⟶ S) (p' : Z ⟶ S') (gb : S' ⟶ S)
    (hfg : h ≫ p = p' ≫ gb) {M : S.Modules} [M.IsQuasicoherent] (n : ℤ)
    (ψ₀ : M ⟶ (Scheme.Modules.pushforward p).obj (G.piece n)) (U : S.Opens)
    (hUa : IsAffineOpen U) (V : S'.Opens) (hVa : IsAffineOpen V) (hV : V ≤ gb ⁻¹ᵁ U)
    (h' : p' ⁻¹ᵁ V ≤ h ⁻¹ᵁ (p ⁻¹ᵁ U))
    (M' : S'.Modules) (hM' : (Scheme.Modules.pullback gb).obj M = M')
    (Alg₂ : RelativeProjTwists.SchemeGradedAlgebra Z)
    (χ₂ : Scheme.Modules.restrict (Alg₂.piece n) k ≅ Bt n)
    (ψ₂ : M' ⟶ (Scheme.Modules.pushforward p').obj (Alg₂.piece n))
    (R : (M').val.obj (op V) →
      (Bt n).val.obj (op (k ⁻¹ᵁ (p' ⁻¹ᵁ V))))
    (h₂ : ∀ a, χ₂.hom.val.app (op (k ⁻¹ᵁ (p' ⁻¹ᵁ V)))
        ((Alg₂.piece n).val.map (homOfLE (k.image_preimage_le (p' ⁻¹ᵁ V))).op
          (ψ₂.val.app (op V) a)) = R a)
    (dχ : M.val.obj (op U) → (N n).val.obj (op ⊤)) (db : M.val.obj (op U) → (Bt n).val.obj (op ⊤))
    (hχ : ∀ a0, (χ n).hom.val.app (op (c ⁻¹ᵁ (p ⁻¹ᵁ U)))
        (pullbackSection c (G.piece n) (p ⁻¹ᵁ U) (c ⁻¹ᵁ (p ⁻¹ᵁ U)) le_rfl
          (ψ₀.val.app (op U) a0)) =
      (N n).val.map (homOfLE le_top).op (dχ a0))
    (htw : ∀ a0, (tw n).val.app (op ⊤)
        (pullbackSection hU (N n) ⊤ ⊤ (fun _ _ => trivial) (dχ a0)) =
      pullbackSection ι (Bt n) ⊤ ⊤ (fun _ _ => trivial) (db a0))
    (sM : M.val.obj (op U) → (M').val.obj (op V))
    (hsM : ∀ a0, HEq (sM a0) (pullbackSection gb M U V hV a0))
    (hb : ∀ a0, (Bt n).val.map (homOfLE le_top).op (db a0) = R (sM a0))
    (χ' : Scheme.Modules.restrict ((pbAlgS h G).piece n) k ≅ Bt n)
    (hχ' : χ' = genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n)
    (ψ' : M' ⟶
      (Scheme.Modules.pushforward p').obj ((pbAlgS h G).piece n))
    (hψ' : HEq ψ' (basePsi p p' gb h hfg ψ₀))
    (a : (M').val.obj (op V)) :
    (chartPsiHom p' k (Bk := (pbAlgS h G).piece n) ψ' χ').val.app (op V) a = R a := by
  subst hM' hχ'
  obtain rfl := eq_of_heq hψ'
  obtain rfl : sM = fun a0 => pullbackSection gb M U V hV a0 :=
    funext fun a0 => eq_of_heq (hsM a0)
  have hb' : ∀ a0, (Bt n).val.map (homOfLE le_top).op (db a0) =
      R (pullbackSection gb M U V hV a0) := hb
  have H := genChartIso_field_aux G h k ρ hU c ι e hρι N Bt χ tw htwIso p p' gb hfg n ψ₀ U hUa V
    hVa hV h' Alg₂ χ₂ ψ₂ R h₂ dχ db hχ htw hb' a
  generalize genChartIso G h k ρ hU c ι e hρι N Bt χ tw htwIso n = C at H ⊢
  generalize basePsi p p' gb h hfg ψ₀ = P at H ⊢
  exact H

end GenericField

section GenericFieldMul

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {R₁ : Type u} {σ : Type w} [CommRing R₁] [SetLike σ R₁] [AddSubgroupClass σ R₁]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y Z D Vv : Scheme.{u}}
  (G : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
  (h : Z ⟶ Y)
  (k : AlgebraicGeometry.Proj 𝒜 ⟶ Z) [IsOpenImmersion k] (ρ : AlgebraicGeometry.Proj 𝒜 ⟶ D)
  (hU : D ⟶ Vv) (c : Vv ⟶ Y) (ι : D ⟶ AlgebraicGeometry.Proj 𝒜)
  (e : k ≫ h = ρ ≫ hU ≫ c) (hρι : ρ ≫ ι = 𝟙 (AlgebraicGeometry.Proj 𝒜))
  (N : ℤ → Vv.Modules)
  (χ : ∀ n, (Scheme.Modules.pullback c).obj (G.piece n) ≅ N n)
  (tw : ∀ n, (Scheme.Modules.pullback hU).obj (N n) ⟶
    (Scheme.Modules.pullback ι).obj (twistingSheaf 𝒜 n))
  (htwIso : ∀ n, IsIso (tw n))

/-- **The chart identification of `h^*G` is multiplicative**, in the form of the canonical
product of the absolute twists, as soon as `χ` and `tw` are. -/
theorem genChartIso_field_mul
    (mulV : ∀ i j, (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩).obj (N i)).obj (N j)) ⟶
      N (i + j))
    (hχm : ∀ i j, TwistMulLeg.pbMul c (gmul G i j) ≫ (χ (i + j)).hom =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Vv.toRingedSpace).presheaf, (Vv.toRingedSpace).IsSheaf⟩)).map
        (((χ i).hom, (χ j).hom) : (_, _) ⟶ (_, _))) ≫ mulV i j)
    (htwm : ∀ i j, TwistMulLeg.pbMul hU (mulV i j) ≫ tw (i + j) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(D.toRingedSpace).presheaf, (D.toRingedSpace).IsSheaf⟩)).map
        ((tw i, tw j) : (_, _) ⟶ (_, _))) ≫
        TwistMulLeg.pbMul ι
          (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 i j))
    (χ' : ∀ n, Scheme.Modules.restrict ((pbAlgS h G).piece n) k ≅ twistingSheaf 𝒜 n)
    (hχ' : χ' = fun n => genChartIso G h k ρ hU c ι e hρι N (fun n => twistingSheaf 𝒜 n)
      χ tw htwIso n)
    (i j : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (x : ((pbAlgS h G).piece i).val.obj (op (k ''ᵁ U)))
    (y : ((pbAlgS h G).piece j).val.obj (op (k ''ᵁ U))) :
    (χ' (i + j)).hom.val.app (op U) (((pbAlgS h G).mul i j).app (op (k ''ᵁ U)) x y) =
      RelativeProjTwists.absoluteTwistProduct 𝒜 i j U ((χ' i).hom.val.app (op U) x)
        ((χ' j).hom.val.app (op U) y) := by
  subst hχ'
  have H := genChartIso_hom_mul G h k ρ hU c ι e hρι N (fun n => twistingSheaf 𝒜 n) χ tw htwIso
    mulV (fun i j => Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 i j)
    hχm htwm i j U x y
  beta_reduce
  generalize genChartIso G h k ρ hU c ι e hρι N (fun n => twistingSheaf 𝒜 n) χ tw htwIso
    (i + j) = C₃
    at H ⊢
  generalize genChartIso G h k ρ hU c ι e hρι N (fun n => twistingSheaf 𝒜 n) χ tw htwIso i = C₁
    at H ⊢
  generalize genChartIso G h k ρ hU c ι e hρι N (fun n => twistingSheaf 𝒜 n) χ tw htwIso j = C₂
    at H ⊢
  exact H

end GenericFieldMul

/-! ### The concrete data -/

section Concrete

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- The base-change morphism `Proj_{S'}(g^*A) ⟶ Proj_S(A)` commutes with the structure
morphisms to `S'` and `S`. -/
theorem baseChangeHom_comp_toBase :
    baseChangeHom A g ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ≫ g :=
  (isPullback_baseChangeHom A g).w

/-- Tag 01NR's chart identification on a pulled-back homogeneous section is the restriction of
Tag 01MP's homogeneous section. -/
theorem chartTwistIso_pullbackSection_psi (V : baseChangeBasis g) (k : ℕ)
    (a : A.sectionPieces (baseOpen V).toOpens k) :
    (chartTwistIso A (k : ℤ) (affOf V)).hom.val.app
        (op (chartU A g V ⁻¹ᵁ ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ
          (baseOpen V).toOpens)))
        (pullbackSection (chartU A g V) (relativeTwist A (k : ℤ))
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ (baseOpen V).toOpens)
          _ le_rfl (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k).val.app
            (op (baseOpen V).toOpens) a)) =
      (twistingSheaf (A.grading (affOf V).1) (k : ℤ)).val.map (homOfLE le_top).op
        (degreeSection (A.grading (affOf V).1) k
          ⟨DirectSum.of (A.sectionPieces (affOf V).1) k a, A.of_mem_grading (affOf V).1 a⟩) := by
  have h' : chartU A g V ''ᵁ (chartU A g V ⁻¹ᵁ
      ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ (baseOpen V).toOpens)) ≤
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ (baseOpen V).toOpens :=
    (chartU A g V).image_preimage_le _
  have h1 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (chartU A g V)
    (relativeTwist A (k : ℤ))
    ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ (baseOpen V).toOpens)
    _ le_rfl h' (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k).val.app
      (op (baseOpen V).toOpens) a)
  have h2 := RelativeInvertibleTwist.chartIso_hom_psi A (affOf V).2 k a _ h'
  exact (congrArg (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso (affOf V).1
    (affOf V).2 k).hom.val.app _) h1).trans h2

/-- The preimage of `V` in `Proj_{S'}(g^*A)` lies in the preimage under the base-change
morphism of the preimage of `baseOpen V` in `Proj_S(A)`. -/
theorem preimage_le_baseChangeHom (V : baseChangeBasis g) :
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ⁻¹ᵁ V.1 ≤
      baseChangeHom A g ⁻¹ᵁ ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ
        (baseOpen V).toOpens) := by
  intro x hx
  change ((baseChangeHom A g ≫
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase)) x ∈ (baseOpen V).toOpens
  rw [baseChangeHom_comp_toBase]
  exact le_baseOpen V hx

end Concrete

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
