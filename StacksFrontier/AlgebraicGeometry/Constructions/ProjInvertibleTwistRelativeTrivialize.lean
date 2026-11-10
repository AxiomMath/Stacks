module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeBasis
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeUnit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The inverse image of a trivialized module along a morphism into the trivializing open

Let `M` be a sheaf of modules on a scheme `S`, trivialized over an open `W` with generator `t`,
and let `f : X ⟶ S` be a morphism with `f⁻¹(W) = X`. Then `f^*M ≅ 𝒪_X`, the inverse sending a
function `c` to `c · f^*t`. This is the form in which the tensor factor `π^*ℒ^{⊗ n}` of the
target of clause (1) of Tag 02NC is trivialized over a chart of the relative homogeneous
spectrum.

The isomorphism is built for any left adjoint `Φ` of the direct image along `f`, not only for
`f^*`, so that it applies to the restriction to an open immersion `j` of an inverse image along
`π`, with `f = j ≫ π`. Its inverse is the morphism `𝒪_X ⟶ Φ M` of multiplication by the pulled
back generator, and its forward map is adjoint to the morphism `M ⟶ f_*𝒪_X` taking a section to
its coordinate in the trivialization, pulled back along `f`. Both composites are checked on
sections: the first on the unit section, the second after the unit of the adjunction.

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackTrivialization.iso`: `Φ M ≅ 𝒪_X`.
* `Stacks.AlgebraicGeometry.PullbackTrivialization.tensorFactorIso`: for an open immersion `j`
  with `j ≫ π` landing in `W`, the restriction along `j` of `F ⊗ π^*M` is the restriction of
  `F`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.chartTensorFactorIso`: the same on the chart
  of `Proj_S(𝒜)` over an affine open of the base, for `F = 𝒪_P(n)`.

## Main results

* `Stacks.AlgebraicGeometry.PullbackTrivialization.iso_inv_app`,
  `tensorFactorIso_inv_app`, `chartTensorFactorIso_inv_app`: the inverses on sections, the last
  being `s ↦ s ⊗ π^*t`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry
open Stacks.SheafOfModules.TensorGenerator

universe u

namespace Stacks.AlgebraicGeometry.PullbackTrivialization

variable {S : Scheme.{u}} {W : S.Opens} (M : S.Modules)
  (e : M.over W ≅ SheafOfModules.unit
    (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
      S.sheaf.obj S.ringCatSheaf.property W))

/-- The canonical generator of the trivialization, a section of `M` over `W`. -/
abbrev gen : Γ(M, W) := generator S.sheaf.obj S.ringCatSheaf.property W M e

/-- The generator restricted to an open `U ⊆ W`. -/
abbrev genAt {U : S.Opens} (h : U ≤ W) : Γ(M, U) := M.val.map (homOfLE h).op (gen M e)

/-- The coordinate of a section of `M` over an open `U ⊆ W` in the trivialization restricted to
`U`: the function on `U` whose multiple of the restricted generator the section is. -/
def coeff {U : S.Opens} (h : U ≤ W) (m : Γ(M, U)) : Γ(S, U) :=
  coord S.sheaf.obj S.ringCatSheaf.property U M (Stacks.SheafOfModules.overIsoRestrict M h e) m

/-- A section is its coordinate times the restricted generator. -/
theorem coeff_smul {U : S.Opens} (h : U ≤ W) (m : Γ(M, U)) :
    coeff M e h m • genAt M e h = m := by
  refine Eq.trans ?_ (smul_generator S.sheaf.obj S.ringCatSheaf.property U M
    (Stacks.SheafOfModules.overIsoRestrict M h e) m)
  exact congrArg (fun z => coeff M e h m • z)
    (Stacks.AlgebraicGeometry.RelativeInvertibleTwist.generator_overIsoRestrict h M e).symm

/-- The coordinate is the unique function whose multiple of the restricted generator is the
section. -/
theorem coeff_eq {U : S.Opens} (h : U ≤ W) {m : Γ(M, U)} {c : Γ(S, U)}
    (hc : c • genAt M e h = m) : coeff M e h m = c := by
  refine (bijective_smul_generator S.sheaf.obj S.ringCatSheaf.property U M
    (Stacks.SheafOfModules.overIsoRestrict M h e)).1 ?_
  have hg := Stacks.AlgebraicGeometry.RelativeInvertibleTwist.generator_overIsoRestrict h M e
  refine Eq.trans ?_ (congrArg (fun z : Γ(M, U) => c • z) hg).symm
  refine Eq.trans (congrArg (fun z : Γ(M, U) => coeff M e h m • z) hg) ?_
  exact (coeff_smul M e h m).trans hc.symm

/-- The coordinate of the generator is `1`. -/
theorem coeff_genAt {U : S.Opens} (h : U ≤ W) : coeff M e h (genAt M e h) = 1 :=
  coeff_eq M e h (one_smul _ _)

/-- The coordinate is additive. -/
theorem coeff_add {U : S.Opens} (h : U ≤ W) (m m' : Γ(M, U)) :
    coeff M e h (m + m') = coeff M e h m + coeff M e h m' :=
  coeff_eq M e h ((add_smul _ _ _).trans (congrArg₂ (· + ·) (coeff_smul M e h m)
    (coeff_smul M e h m')))

/-- The coordinate is linear over the functions. -/
theorem coeff_smul_left {U : S.Opens} (h : U ≤ W) (r : Γ(S, U)) (m : Γ(M, U)) :
    coeff M e h (r • m) = r * coeff M e h m :=
  coeff_eq M e h ((mul_smul _ _ _).trans (congrArg (fun z : Γ(M, U) => r • z)
    (coeff_smul M e h m)))

/-- Two restriction maps of a sheaf of modules compose to the restriction map along the composite
inclusion. -/
private theorem map_map_homOfLE {Z : Scheme.{u}} (N : Z.Modules) {O₁ O₂ O₃ : Z.Opens}
    (h₁ : O₂ ≤ O₁) (h₂ : O₃ ≤ O₂) (h₃ : O₃ ≤ O₁) (y : Γ(N, O₁)) :
    N.presheaf.map (homOfLE h₂).op (N.presheaf.map (homOfLE h₁).op y) =
      N.presheaf.map (homOfLE h₃).op y :=
  (PresheafOfModules.map_comp_apply N.val (homOfLE h₁).op (homOfLE h₂).op y).symm.trans
    (PresheafOfModules.congr_map_apply N.val (Subsingleton.elim _ _) y)

/-- The coordinate commutes with restriction. -/
theorem coeff_res {U U' : S.Opens} (h : U ≤ W) (h' : U' ≤ U) (m : Γ(M, U)) :
    coeff M e (h'.trans h) (M.presheaf.map (homOfLE h').op m) =
      S.presheaf.map (homOfLE h').op (coeff M e h m) := by
  refine coeff_eq M e (h'.trans h) ?_
  refine Eq.trans ?_ (congrArg (M.presheaf.map (homOfLE h').op) (coeff_smul M e h m))
  refine Eq.trans ?_ (Scheme.Modules.map_smul M (homOfLE h') _ _).symm
  refine congrArg (fun z : Γ(M, U') => S.presheaf.map (homOfLE h').op (coeff M e h m) • z) ?_
  exact (map_map_homOfLE M h h' _ (gen M e)).symm

/-! ### The inverse, as the adjoint of a map to the direct image of the structure sheaf -/

variable {X : Scheme.{u}} (f : X ⟶ S) (hW : f ⁻¹ᵁ W = ⊤)

include hW in
/-- As `f⁻¹(W)` is everything, `f⁻¹(U) = f⁻¹(U ∩ W)`. -/
theorem preimage_le_preimage_inf (U : S.Opens) : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ (U ⊓ W) := fun x hx =>
  ⟨hx, show x ∈ f ⁻¹ᵁ W from hW ▸ trivial⟩

/-- The coordinate of a section over `U`, read over `U ∩ W` and pulled back along `f` to
`f^{-1}U = f^{-1}(U ∩ W)`. -/
def rhoApp (U : S.Opens) (m : Γ(M, U)) : Γ(X, f ⁻¹ᵁ U) :=
  f.appLE (U ⊓ W) (f ⁻¹ᵁ U) (preimage_le_preimage_inf f hW U)
    (coeff M e inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m))

/-- `rhoApp` is additive. -/
theorem rhoApp_add (U : S.Opens) (m m' : Γ(M, U)) :
    rhoApp M e f hW U (m + m') = rhoApp M e f hW U m + rhoApp M e f hW U m' := by
  simp only [rhoApp, map_add, coeff_add]

/-- `rhoApp` is semilinear along `f`. -/
theorem rhoApp_smul (U : S.Opens) (r : Γ(S, U)) (m : Γ(M, U)) :
    rhoApp M e f hW U (r • m) = f.app U r * rhoApp M e f hW U m := by
  simp only [rhoApp, Scheme.Modules.map_smul, coeff_smul_left, map_mul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_eq_app]

/-- `rhoApp` commutes with restriction. -/
theorem rhoApp_res {U U' : S.Opens} (h : U' ≤ U) (m : Γ(M, U)) :
    rhoApp M e f hW U' (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op (rhoApp M e f hW U m) := by
  have h' : U' ⊓ W ≤ U ⊓ W := inf_le_inf_right W h
  have hc := coeff_res M e (inf_le_right : U ⊓ W ≤ W) h' (M.presheaf.map (homOfLE inf_le_left).op m)
  have hm : M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE inf_le_left).op m) =
      M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map (homOfLE h).op m) := by
    rw [map_map_homOfLE _ _ _ (h'.trans inf_le_left), map_map_homOfLE]
  simp only [rhoApp]
  rw [← hm, hc, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

/-- The coordinate map, as a morphism of sheaves of modules from `M` to the direct image of the
structure sheaf of `X`. -/
def rho : M ⟶ (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.AlgebraicGeometry.ModuleLimits.homOfSections (rhoApp M e f hW) (rhoApp_add M e f hW)
    (rhoApp_smul M e f hW) fun _ _ h m => rhoApp_res M e f hW h m

/-! ### The generator, pulled back -/

variable {Φ : S.Modules ⥤ X.Modules} (adj : Φ ⊣ Scheme.Modules.pushforward f)

/-- The generator of the trivialization, carried along the unit of the adjunction to a global
section of `Φ M`; for `Φ = f^*` this is `f^*t`. -/
def genTop : Γ(Φ.obj M, ⊤) :=
  (Φ.obj M).presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ W from hW.ge)).op
    ((adj.unit.app M).app W (gen M e))

/-- The pulled-back generator, restricted to an open of `X`. -/
abbrev genTopAt (V : X.Opens) : Γ(Φ.obj M, V) :=
  (Φ.obj M).presheaf.map (homOfLE le_top).op (genTop M e f hW adj)

/-- **The trivialization of `Φ M`, in the direction `𝒪_X ⟶ Φ M`**: a function `c` on an open `V`
goes to `c` times the pulled-back generator. -/
def sigma : SheafOfModules.unit X.ringCatSheaf ⟶ Φ.obj M :=
  Stacks.AlgebraicGeometry.ModuleLimits.homOfSections
    (fun V (c : Γ(X, V)) => c • genTopAt M e f hW adj V)
    (fun V c c' => add_smul (show Γ(X, V) from c) (show Γ(X, V) from c')
      (genTopAt M e f hW adj V))
    (fun V r c => mul_smul r (show Γ(X, V) from c) (genTopAt M e f hW adj V))
    (fun V V' h c => by
      refine Eq.trans ?_ (Scheme.Modules.map_smul (Φ.obj M) (homOfLE h) c _).symm
      refine congrArg (fun z => (X.presheaf.map (homOfLE h).op c) • z) ?_
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl)

/-- The pulled-back generator restricts to the pulled-back generator. -/
theorem genTopAt_res {V V' : X.Opens} (h : V' ≤ V) :
    (Φ.obj M).presheaf.map (homOfLE h).op (genTopAt M e f hW adj V) =
      genTopAt M e f hW adj V' := by
  exact map_map_homOfLE _ _ _ _ _

/-- The unit of the adjunction carries the restricted generator to the restricted pulled-back
generator. -/
theorem unit_genAt {U : S.Opens} (h : U ≤ W) :
    (adj.unit.app M).app U (genAt M e h) = genTopAt M e f hW adj (f ⁻¹ᵁ U) := by
  have hn := PresheafOfModules.naturality_apply (adj.unit.app M).val (homOfLE h).op (gen M e)
  refine hn.trans ?_
  exact (map_map_homOfLE _ _ _ _ _).symm

/-- `rhoApp` read over `f⁻¹(U ∩ W)`. -/
theorem rhoApp_res_inf (U : S.Opens) (m : Γ(M, U)) :
    X.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : U ⊓ W ≤ U))).op
        (rhoApp M e f hW U m) =
      f.app (U ⊓ W) (coeff M e inf_le_right (M.presheaf.map (homOfLE inf_le_left).op m)) := by
  simp only [rhoApp]
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, ← Scheme.Hom.appLE_eq_app]

/-- The morphism `Φ M ⟶ 𝒪_X` adjoint to the coordinate map. -/
def rhoAdj : Φ.obj M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (adj.homEquiv M (SheafOfModules.unit X.ringCatSheaf)).symm (rho M e f hW)

/-- `rhoAdj` after the unit of the adjunction is `rhoApp`. -/
theorem rhoAdj_app_unit (U : S.Opens) (m : Γ(M, U)) :
    (rhoAdj M e f hW adj).app (f ⁻¹ᵁ U) ((adj.unit.app M).app U m) = rhoApp M e f hW U m := by
  have h := (adj.homEquiv M (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply
    (rho M e f hW)
  have h2 := (adj.homEquiv_unit M (SheafOfModules.unit X.ringCatSheaf)
    (rhoAdj M e f hW adj)).symm.trans h
  exact congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit X.ringCatSheaf) => φ.app U m) h2

/-- The coordinate map takes the generator to `1`. -/
theorem rhoApp_genAt : rhoApp M e f hW W (genAt M e le_rfl) = 1 := by
  have h1 : M.presheaf.map (homOfLE (inf_le_left : W ⊓ W ≤ W)).op (genAt M e le_rfl) =
      genAt M e (inf_le_right : W ⊓ W ≤ W) :=
    map_map_homOfLE _ _ _ _ _
  simp only [rhoApp]
  rw [h1, coeff_genAt, map_one]

/-- The unit section of the structure sheaf over an open. -/
abbrev oneAt (V : X.Opens) : Γ(SheafOfModules.unit X.ringCatSheaf, V) :=
  show Γ(X, V) from 1

/-- `rhoAdj` takes the pulled-back generator to `1`. -/
theorem rhoAdj_genTopAt (V : X.Opens) :
    (rhoAdj M e f hW adj).app V (genTopAt M e f hW adj V) = oneAt V := by
  have h0 : (rhoAdj M e f hW adj).app (f ⁻¹ᵁ W) (genTopAt M e f hW adj (f ⁻¹ᵁ W)) =
      oneAt (f ⁻¹ᵁ W) := by
    rw [← unit_genAt M e f hW adj le_rfl, rhoAdj_app_unit, rhoApp_genAt]
  have hV : V ≤ f ⁻¹ᵁ W := hW ▸ le_top
  rw [← genTopAt_res M e f hW adj hV]
  have hn := PresheafOfModules.naturality_apply (rhoAdj M e f hW adj).val (homOfLE hV).op
    (genTopAt M e f hW adj (f ⁻¹ᵁ W))
  refine hn.trans ?_
  refine (congrArg (X.presheaf.map (homOfLE hV).op) h0).trans ?_
  exact (X.presheaf.map (homOfLE hV).op).hom.map_one

/-- Multiplication by the pulled-back generator, then the coordinate, is the identity. -/
theorem sigma_rhoAdj :
    sigma M e f hW adj ≫ rhoAdj M e f hW adj = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext c
  refine (Scheme.Modules.Hom.app_smul (rhoAdj M e f hW adj) (show Γ(X, V) from c)
    (genTopAt M e f hW adj V)).trans ?_
  rw [rhoAdj_genTopAt M e f hW adj V]
  exact mul_one (show Γ(X, V) from c)

/-- The unit of the adjunction is semilinear along `f`. -/
theorem unit_smul (U : S.Opens) (c : Γ(S, U)) (m : Γ(M, U)) :
    (adj.unit.app M).app U (c • m) =
      f.app U c • (show Γ(Φ.obj M, f ⁻¹ᵁ U) from (adj.unit.app M).app U m) :=
  ((adj.unit.app M).val.app (op U)).hom.map_smul c m

/-- A restriction map along an equality of opens, written as two inclusions, is injective. -/
theorem res_injective {V V' : X.Opens} (h : V' ≤ V) (h' : V ≤ V') (N : X.Modules) :
    Function.Injective (N.presheaf.map (homOfLE h).op) := by
  intro a b hab
  have key : ∀ z : Γ(N, V),
      N.presheaf.map (homOfLE h').op (N.presheaf.map (homOfLE h).op z) = z := fun z => by
    rw [map_map_homOfLE _ _ _ le_rfl]
    exact PresheafOfModules.map_id_apply N.val _ z
  rw [← key a, ← key b, hab]

/-- Multiplying the coordinate of a section by the pulled-back generator gives back the pulled-back
section. -/
theorem sigma_app_rhoApp (U : S.Opens) (m : Γ(M, U)) :
    Scheme.Modules.Hom.app (sigma M e f hW adj) (f ⁻¹ᵁ U) (rhoApp M e f hW U m) =
      (adj.unit.app M).app U m := by
  have hle : f ⁻¹ᵁ (U ⊓ W) ≤ f ⁻¹ᵁ U := f.preimage_mono inf_le_left
  refine res_injective hle (preimage_le_preimage_inf f hW U) (Φ.obj M) ?_
  change (Φ.obj M).presheaf.map (homOfLE hle).op
      ((show Γ(X, f ⁻¹ᵁ U) from rhoApp M e f hW U m) • genTopAt M e f hW adj (f ⁻¹ᵁ U)) = _
  rw [Scheme.Modules.map_smul, genTopAt_res, rhoApp_res_inf, ← unit_genAt M e f hW adj
    (inf_le_right : U ⊓ W ≤ W), ← unit_smul, coeff_smul]
  exact (PresheafOfModules.naturality_apply (adj.unit.app M).val (homOfLE inf_le_left).op m)

/-- The coordinate, then multiplication by the pulled-back generator, is the identity. -/
theorem rhoAdj_sigma : rhoAdj M e f hW adj ≫ sigma M e f hW adj = 𝟙 (Φ.obj M) := by
  apply (adj.homEquiv M (Φ.obj M)).injective
  refine (adj.homEquiv_naturality_right (rhoAdj M e f hW adj) (sigma M e f hW adj)).trans ?_
  refine Eq.trans ?_ (adj.homEquiv_id M).symm
  refine (congrArg (fun φ => φ ≫ (Scheme.Modules.pushforward f).map (sigma M e f hW adj))
    ((adj.homEquiv M (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply
      (rho M e f hW))).trans ?_
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  exact sigma_app_rhoApp M e f hW adj U m

/-- **The inverse image of a module trivialized over `W` along a morphism landing in `W` is
trivial**: `Φ M ≅ 𝒪_X`, for `Φ` any left adjoint of the direct image along `f` (for instance
`f^*`). Its inverse sends a function `c` to `c` times the pulled-back generator. -/
def iso : Φ.obj M ≅ SheafOfModules.unit X.ringCatSheaf where
  hom := rhoAdj M e f hW adj
  inv := sigma M e f hW adj
  hom_inv_id := rhoAdj_sigma M e f hW adj
  inv_hom_id := sigma_rhoAdj M e f hW adj

/-- The inverse of `iso` on sections: `c ↦ c · f^*t`. -/
theorem iso_inv_app (V : X.Opens) (c : Γ(X, V)) :
    Scheme.Modules.Hom.app (iso M e f hW adj).inv V c = c • genTopAt M e f hW adj V :=
  rfl

/-! ### The tensor factor on an open immersion into a scheme over the trivializing open -/

section TensorFactor

open MonoidalCategory
open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {P Y : Scheme.{u}} (π : P ⟶ S) (j : Y ⟶ P) [IsOpenImmersion j]

/-- Restriction along `j` after the inverse image along `π` is left adjoint to the direct image
along `j ≫ π`. -/
def restrictPullbackAdj :
    (Scheme.Modules.pullback π ⋙ Scheme.Modules.restrictFunctor j) ⊣
      Scheme.Modules.pushforward (j ≫ π) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction π).comp
    (Scheme.Modules.restrictAdjunction j)).ofNatIsoRight (Scheme.Modules.pushforwardComp j π)

variable (hV : (j ≫ π) ⁻¹ᵁ W = ⊤)

/-- **The restriction along `j` of `π^*M` is trivial**, for `j ≫ π` landing in the open `W`
over which `M` is trivialized. -/
def restrictPullbackIso :
    (Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pullback π).obj M) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  iso M e (j ≫ π) hV (restrictPullbackAdj π j)

/-- `restrictPullbackIso`, read in the monoidal category of sheaves of modules over the
ringed-space spelling of the structure sheaf, with the structure sheaf as its unit object. -/
def restrictPullbackIsoUnit :
    ofScheme ((Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pullback π).obj M)) ≅
      𝟙_ (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) :=
  restrictPullbackIso M e π j hV

/-- The right unitor of the monoidal structure on sheaves of modules on `Y`. -/
def rightUnitorY (G : Y.Modules) :
    ofScheme G ⊗ 𝟙_ (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) ≅
      ofScheme G :=
  ρ_ (ofScheme G)

/-- **The tensor factor, trivialized on the open immersion**: the restriction along `j` of
`F ⊗ π^*M` is the restriction of `F`, for `j ≫ π` landing in the open `W` over which `M` is
trivialized. -/
def tensorFactorIso (F : P.Modules) :
    (Scheme.Modules.restrictFunctor j).obj (tensorMod F ((Scheme.Modules.pullback π).obj M)) ≅
      (Scheme.Modules.restrictFunctor j).obj F :=
  Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F
      ((Scheme.Modules.pullback π).obj M) ≪≫
    whiskerLeftIso (ofScheme ((Scheme.Modules.restrictFunctor j).obj F))
      (restrictPullbackIsoUnit M e π j hV) ≪≫
    rightUnitorY ((Scheme.Modules.restrictFunctor j).obj F)

/-- Three restriction maps of a sheaf of modules compose to the restriction map along the
composite inclusion. -/
theorem map₃_eq (N : P.Modules) {O₁ O₂ O₃ O₄ : P.Opens} (a : op O₁ ⟶ op O₂) (b : op O₂ ⟶ op O₃)
    (c : op O₃ ⟶ op O₄) (d : op O₁ ⟶ op O₄) (y : N.val.obj (op O₁)) :
    N.val.map c (N.val.map b (N.val.map a y)) = N.val.map d y :=
  (PresheafOfModules.map_comp_apply N.val b c _).symm.trans
    ((PresheafOfModules.map_comp_apply N.val a (b ≫ c) y).symm.trans
      (PresheafOfModules.congr_map_apply N.val (Subsingleton.elim _ _) y))

include hV in
/-- The image of an open under `j` lies in the inverse image of `W`. -/
theorem image_le_preimage (U : Y.Opens) : j ''ᵁ U ≤ π ⁻¹ᵁ W := by
  rintro _ ⟨y, -, rfl⟩
  exact show y ∈ (j ≫ π) ⁻¹ᵁ W from hV ▸ trivial

/-- The unit of `restrictPullbackAdj` is the unit of the inverse image along `π` followed by the
direct image of the unit of the restriction along `j`. -/
theorem restrictPullbackAdj_unit :
    (restrictPullbackAdj π j).unit.app M =
      (Scheme.Modules.pullbackPushforwardAdjunction π).unit.app M ≫
        (Scheme.Modules.pushforward π).map
          ((Scheme.Modules.restrictAdjunction j).unit.app ((Scheme.Modules.pullback π).obj M)) ≫
        (Scheme.Modules.pushforwardComp j π).hom.app _ := by
  simp only [restrictPullbackAdj, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc]
  rfl

/-- The unit of `restrictPullbackAdj` on sections: the unit of the inverse image along `π`,
restricted to the image of the open. -/
theorem restrictPullbackAdj_unit_app (U : S.Opens) (m : Γ(M, U)) :
    ((restrictPullbackAdj π j).unit.app M).app U m =
      ((Scheme.Modules.pullback π).obj M).presheaf.map
        (homOfLE (j.image_preimage_le (π ⁻¹ᵁ U))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app M).app U m) :=
  congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward (j ≫ π)).obj
      ((Scheme.Modules.restrictFunctor j).obj ((Scheme.Modules.pullback π).obj M)) =>
    φ.app U m) (restrictPullbackAdj_unit M π j)

/-- The pulled-back generator for `restrictPullbackAdj` is the restriction of `π^*t`. -/
theorem genTopAt_restrictPullbackAdj (U : Y.Opens) :
    genTopAt M e (j ≫ π) hV (restrictPullbackAdj π j) U =
      ((Scheme.Modules.pullback π).obj M).presheaf.map
        (homOfLE (image_le_preimage π j hV U)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app M).app W (gen M e)) := by
  simp only [genTopAt, genTop]
  rw [restrictPullbackAdj_unit_app]
  exact map₃_eq ((Scheme.Modules.pullback π).obj M) _ _ _ _ _

/-- The inverse of the right unitor on a section: `s ↦ s ⊗ 1`. -/
theorem rightUnitorY_inv_app (G : Y.Modules) (U : Y.Opens) (s : Γ(G, U)) :
    (rightUnitorY G).inv.val.app (op U) s =
      Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace (ofScheme G) _ (op U) s
        (Stacks.PullbackTensorCoherence.oneSec Y.toRingedSpace (op U)) := by
  have h := Stacks.PullbackTensorCoherence.rightUnitor_hom_tmul (Z := Y.toRingedSpace) (op U)
    (A := ofScheme G) s (1 : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op U))
  have h' := h.trans (one_smul _ (show (ofScheme G).val.obj (op U) from s))
  refine (congrArg ((rightUnitorY G).inv.val.app (op U)) h'.symm).trans ?_
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app (rightUnitorY G) (op U) _

/-- **The inverse of the trivialized tensor factor on sections**: a section `s` of `F` over the
image of `U` goes to `s ⊗ π^*t`, the pure tensor of `s` with the restriction of the pulled-back
generator. -/
theorem tensorFactorIso_inv_app (F : P.Modules) (U : Y.Opens) (s : Γ(F, j ''ᵁ U)) :
    (tensorFactorIso M e π j hV F).inv.val.app (op U) s =
      gammaTmul F ((Scheme.Modules.pullback π).obj M) (j ''ᵁ U) s
        (((Scheme.Modules.pullback π).obj M).presheaf.map
          (homOfLE (image_le_preimage π j hV U)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app M).app W (gen M e))) := by
  set g := genTopAt M e (j ≫ π) hV (restrictPullbackAdj π j) U with hg
  have e1 := rightUnitorY_inv_app ((Scheme.Modules.restrictFunctor j).obj F) U s
  have e2 := Stacks.PullbackTensorCoherence.whiskerLeft_tmul (Z := Y.toRingedSpace)
    (A := ofScheme ((Scheme.Modules.restrictFunctor j).obj F))
    (restrictPullbackIsoUnit M e π j hV).inv (op U) s
    (Stacks.PullbackTensorCoherence.oneSec Y.toRingedSpace (op U))
  have e2' : (restrictPullbackIsoUnit M e π j hV).inv.val.app (op U)
      (Stacks.PullbackTensorCoherence.oneSec Y.toRingedSpace (op U)) = g :=
    one_smul Γ(Y, U)
      (show Γ((Scheme.Modules.pullback π ⋙ Scheme.Modules.restrictFunctor j).obj M, U) from g)
  have e3 := Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso_hom_unit_tmul j F
    ((Scheme.Modules.pullback π).obj M) U s g
  have e3' := (congrArg ((Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F
    ((Scheme.Modules.pullback π).obj M)).inv.val.app (op U)) e3).symm.trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app
      (Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F
        ((Scheme.Modules.pullback π).obj M)) (op U) _)
  have e4 := genTopAt_restrictPullbackAdj M e π j hV U
  change (Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso j F
      ((Scheme.Modules.pullback π).obj M)).inv.val.app (op U)
      ((whiskerLeftIso (ofScheme ((Scheme.Modules.restrictFunctor j).obj F))
        (restrictPullbackIsoUnit M e π j hV)).inv.val.app (op U)
        ((rightUnitorY ((Scheme.Modules.restrictFunctor j).obj F)).inv.val.app (op U) s)) = _
  rw [e1, whiskerLeftIso_inv, e2, e2']
  refine e3'.trans ?_
  rw [hg, e4]
  rfl

end TensorFactor

end Stacks.AlgebraicGeometry.PullbackTrivialization

/-! ### On a chart of a relative homogeneous spectrum -/

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open Stacks.AlgebraicGeometry.PullbackTrivialization
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S) {V : S.Opens} (hV : IsAffineOpen V)

/-- The chart over an affine open of the base lands in the inverse image of that open. -/
theorem chart_comp_toBase_preimage :
    ((relativeProj 𝒜).chart V hV ≫ (relativeProj 𝒜).toBase) ⁻¹ᵁ V = ⊤ := by
  rw [((relativeProj 𝒜).chart_isPullback V hV).w, Scheme.Hom.comp_preimage, V.ι_preimage_self,
    Scheme.Hom.preimage_top]

/-- **The tensor factor of Tag 02NC's clause (1), trivialized on a chart.** For an affine open
`V` of the base and a trivialization `e` of a module `M` over `V`, the restriction to the chart
`Proj 𝒜(V)` of `𝒪_P(n) ⊗ π^*M` is the restriction of `𝒪_P(n)`; on sections the inverse is
`s ↦ s ⊗ π^*t`, `t` the generator of `e` (`chartTensorFactorIso_inv_app`). -/
def chartTensorFactorIso (n : ℤ) (M : S.Modules)
    (e : M.over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V)) :
    letI := (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chart_isOpenImmersion V hV
    (Scheme.Modules.restrictFunctor ((relativeProj 𝒜).chart V hV)).obj
        (tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj M)) ≅
      (Scheme.Modules.restrictFunctor ((relativeProj 𝒜).chart V hV)).obj
        (Tag07ZGTwist.relativeTwist 𝒜 n) :=
  letI := (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chart_isOpenImmersion V hV
  tensorFactorIso M e (relativeProj 𝒜).toBase ((relativeProj 𝒜).chart V hV)
    (chart_comp_toBase_preimage 𝒜 hV) (Tag07ZGTwist.relativeTwist 𝒜 n)

/-- **The inverse of `chartTensorFactorIso` on sections**: over an open `U` of the chart, a
section `s` of `𝒪_P(n)` over its image goes to the pure tensor of `s` with the restriction of
`π^*t`, `t` the generator of the trivialization. -/
theorem chartTensorFactorIso_inv_app (n : ℤ) (M : S.Modules)
    (e : M.over V ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.SliceRestriction.sliceStructureSheaf
        S.sheaf.obj S.ringCatSheaf.property V))
    (U : (AlgebraicGeometry.Proj (𝒜.grading V)).Opens)
    (s : Γ(Tag07ZGTwist.relativeTwist 𝒜 n, (relativeProj 𝒜).chart V hV ''ᵁ U)) :
    letI := (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chart_isOpenImmersion V hV
    (chartTensorFactorIso 𝒜 hV n M e).inv.val.app (op U) s =
      gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj M)
        ((relativeProj 𝒜).chart V hV ''ᵁ U) s
        (((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj M).presheaf.map
          (homOfLE (image_le_preimage (relativeProj 𝒜).toBase ((relativeProj 𝒜).chart V hV)
            (chart_comp_toBase_preimage 𝒜 hV) U)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj 𝒜).toBase).unit.app
            M).app V (gen M e))) :=
  let := (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chart_isOpenImmersion V hV
  tensorFactorIso_inv_app M e (relativeProj 𝒜).toBase ((relativeProj 𝒜).chart V hV)
    (chart_comp_toBase_preimage 𝒜 hV) (Tag07ZGTwist.relativeTwist 𝒜 n) U s

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
