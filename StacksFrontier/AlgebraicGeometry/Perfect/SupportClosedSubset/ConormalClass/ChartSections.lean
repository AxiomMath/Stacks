module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ConormalClass.ChartFacts

/-!
# The twisted class of a chart, on sections

Let `i : Z ⟶ X` be a closed immersion, `c ≥ 0`, `ℒ = ⋀^c 𝒞_{Z/X}` and `ℱ` a module on `X`.  On a
chart `(W, f)` of `i`, a local section `m` of `i_*(ℒ^∨ ⊗ i^*ℱ)` over an open `U ⊆ W` has a class
in `ℋ^c_Z(ℱ)(U)`: evaluate the functional at the wedge `ω_f` to get a section of `i_*i^*ℱ`,
apply the class `c̄_{W,f}` of Stacks 0G7Q, and read the result back in `ℋ^c_Z(ℱ)` through the
change of support `ℋ^c_Z ⟶ ℋ^c_{T_{W,f}}`, which is an isomorphism over `W`.  These local maps
are additive, `𝒪_X`-linear and compatible with restriction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.Perfect.SupportedFraction (supportCohomologySheaf supportCohomologySheafMap)

universe u

namespace Stacks.Perfect.ConormalClass

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] modulesMonoidal

variable {X : Scheme.{u}}

/-- An open contained in `V` lies inside the image of its preimage in `V`. -/
theorem le_image_preimage {Y : Scheme.{u}} {V P : Y.Opens} (h : P ≤ V) :
    P ≤ V.ι ''ᵁ (V.ι ⁻¹ᵁ P) := by
  rw [V.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf h le_rfl

/-- An open contained in `V` is the image of its preimage in `V`. -/
theorem image_preimage_eq {Y : Scheme.{u}} {V P : Y.Opens} (h : P ≤ V) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ P) = P := by
  rw [V.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 h

/-- A morphism of modules commutes with restriction, on sections. -/
theorem hom_app_map {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N) {U' U : Y.Opens} (h : U' ≤ U)
    (m : Γ(M, U)) :
    φ.app U' (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (φ.app U m) :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) m).trans
      (ConcreteCategory.comp_apply _ _ _))

/-- **Over an open meeting `T'` only inside `T`, the change of support is bijective on
sections.** -/
theorem bijective_supportChangeH_app {T T' : Set X} (hT : IsClosed T) (hT' : IsClosed T')
    (hTT' : T ⊆ T') (W : X.Opens) (hW : ∀ x ∈ W, x ∈ T' → x ∈ T) (F : X.Modules) (p : ℤ)
    {U : X.Opens} (hU : U ≤ W) :
    Function.Bijective ((supportChangeH hT hT' hTT' F p).app U) := by
  have hiso : IsIso ((res W).map (supportChangeH hT hT' hTT' F p)) :=
    isIso_res_homology_supportChange hTT' W hW hT hT'
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) p
  have h2 : IsIso ((supportChangeH hT hT' hTT' F p).app (W.ι ''ᵁ (W.ι ⁻¹ᵁ U))) :=
    inferInstanceAs (IsIso (((res W).map (supportChangeH hT hT' hTT' F p)).app (W.ι ⁻¹ᵁ U)))
  rw [image_preimage_eq hU] at h2
  exact ConcreteCategory.bijective_of_isIso _

/-- Restricting the value of a map into `j_*(G|_V)` on a sum is the sum of the restricted
values. -/
private theorem push_res_map_add {Y : Scheme.{u}} {V P : Y.Opens} {M G : Y.Modules}
    (φ : M ⟶ (push V).obj ((res V).obj G)) (hP : P ≤ V) (m m' : Γ(M, P)) :
    G.presheaf.map (homOfLE (le_image_preimage hP)).op (φ.app P (m + m')) =
      G.presheaf.map (homOfLE (le_image_preimage hP)).op (φ.app P m) +
        G.presheaf.map (homOfLE (le_image_preimage hP)).op (φ.app P m') :=
  (congrArg (G.presheaf.map (homOfLE (le_image_preimage hP)).op).hom
    ((φ.app P).hom.map_add m m')).trans (map_add _ _ _)

section ChartSec

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ) (F : X.Modules)

/-- **The determinant line `ℒ = ⋀^c 𝒞_{Z/X}`** of the conormal sheaf. -/
abbrev line : Z.Modules := Scheme.Modules.exteriorPower (conormal i) c

/-- **The source `i_*(ℒ^∨ ⊗_{𝒪_Z} i^*ℱ)` of the canonical map of Stacks 0G7T.** -/
abbrev twistSource : X.Modules :=
  (Scheme.Modules.pushforward i).obj (dualModule (line i c) ⊗ (Scheme.Modules.pullback i).obj F)

/-- The module `i_*i^*ℱ`. -/
abbrev quotPull : X.Modules :=
  (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)

variable {i c} {W : X.Opens} {f : Fin c → Γ(X, W)}
  (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom i) W f)

/-- The wedge `ω_f` of a chart. -/
abbrev chartWedge : Γ(line i c, i ⁻¹ᵁ W) := wedge i f (app_chart_eq_zero W f hgen)

/-- The evaluation at `ω_f` of a local section of `i_*(ℒ^∨ ⊗ i^*ℱ)`, a local section of
`i_*i^*ℱ`. -/
def chartEvalSec (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U)) : Γ(quotPull i F, U) :=
  ((Scheme.Modules.pullback i).obj F).presheaf.map
    (homOfLE (le_image_preimage (i.preimage_mono hU))).op
    ((evalAt (line i c) ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ W)
      (chartWedge hgen)).app (i ⁻¹ᵁ U) m)

/-- The class `c̄_{W,f}` of Stacks 0G7Q, on a local section of `i_*i^*ℱ`. -/
def chartDescSec (U : X.Opens) (hU : U ≤ W) (y : Γ(quotPull i F, U)) :
    Γ(supportCohomologySheaf (isClosed_chartSupport W (chartEq W f)) F (c : ℤ), U) :=
  (supportCohomologySheaf (isClosed_chartSupport W (chartEq W f)) F (c : ℤ)).presheaf.map
    (homOfLE (le_image_preimage hU)).op
    ((chartDescent i W f F hgen (isClosed_chartSupport W (chartEq W f)) subset_rfl).app U y)

/-- The change of support `ℋ^c_Z(ℱ) ⟶ ℋ^c_{T_{W,f}}(ℱ)` of a chart. -/
abbrev chartTheta :
    supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ) ⟶
      supportCohomologySheaf (isClosed_chartSupport W (chartEq W f)) F (c : ℤ) :=
  supportChangeH (isClosed_zeroLocus i) (isClosed_chartSupport W (chartEq W f))
    (zeroLocus_subset_chartSupport W f hgen) F (c : ℤ)

/-- Over an open `U ⊆ W`, the change of support `chartTheta` is bijective on sections. -/
theorem bijective_chartTheta_app {U : X.Opens} (hU : U ≤ W) :
    Function.Bijective ((chartTheta F hgen).app U) :=
  bijective_supportChangeH_app _ _ _ W
    (fun x hx hxT => mem_zeroLocus_of_mem_chartSupport W f hgen x hx hxT) F _ hU

/-- **The class of a chart on a local section of `i_*(ℒ^∨ ⊗ i^*ℱ)`**, in `ℋ^c_Z(ℱ)`. -/
def chartSec (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U)) :
    Γ(supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ), U) :=
  (Equiv.ofBijective _ (bijective_chartTheta_app F hgen hU)).symm
    (chartDescSec F hgen U hU (chartEvalSec F hgen U hU m))

/-- The change of support sends `chartSec m` to `chartDescSec (chartEvalSec m)`. -/
theorem chartTheta_chartSec (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U)) :
    (chartTheta F hgen).app U (chartSec F hgen U hU m) =
      chartDescSec F hgen U hU (chartEvalSec F hgen U hU m) :=
  (Equiv.ofBijective _ (bijective_chartTheta_app F hgen hU)).apply_symm_apply _

/-- A section `z` of `ℋ^c_Z(ℱ)` equals `chartSec m` if and only if its image under the change
of support is `chartDescSec (chartEvalSec m)`. -/
theorem chartSec_eq_iff (U : X.Opens) (hU : U ≤ W) (m : Γ(twistSource i c F, U))
    (z : Γ(supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ), U)) :
    chartSec F hgen U hU m = z ↔
      (chartTheta F hgen).app U z = chartDescSec F hgen U hU (chartEvalSec F hgen U hU m) := by
  refine ⟨fun h => h ▸ chartTheta_chartSec F hgen U hU m, fun h => ?_⟩
  exact (bijective_chartTheta_app F hgen hU).1 ((chartTheta_chartSec F hgen U hU m).trans h.symm)

/-! ### Linearity and compatibility with restriction -/

/-- `chartEvalSec` is additive. -/
theorem chartEvalSec_add (U : X.Opens) (hU : U ≤ W) (m m' : Γ(twistSource i c F, U)) :
    chartEvalSec F hgen U hU (m + m') = chartEvalSec F hgen U hU m + chartEvalSec F hgen U hU m' :=
  push_res_map_add _ (i.preimage_mono hU) m m'

/-- A restriction followed by a restriction back to the same open is the identity on functions. -/
theorem presheaf_map_map_self {Y : Scheme.{u}} {A B : Y.Opens} (a : B ⟶ A) (b : A ⟶ B)
    (r : Γ(Y, A)) : Y.presheaf.map b.op (Y.presheaf.map a.op r) = r := by
  refine (presheaf_map_map_eq Y.presheaf a.op b.op (𝟙 _) (𝟙 _) r).trans ?_
  rw [Y.presheaf.map_id]
  rfl

/-- Restricting the value of a `𝒪_Y`-linear map into `j_*(G|_V)` commutes with scalars. -/
private theorem push_res_map_smul {Y : Scheme.{u}} {V P : Y.Opens} {M G : Y.Modules}
    (φ : M ⟶ (push V).obj ((res V).obj G)) (hP : P ≤ V) (r : Γ(Y, P)) (m : Γ(M, P)) :
    G.presheaf.map (homOfLE (le_image_preimage hP)).op (φ.app P (r • m)) =
      r • G.presheaf.map (homOfLE (le_image_preimage hP)).op (φ.app P m) := by
  have h2 := push_res_smul V G P r (φ.app P m)
  rw [Scheme.Modules.Hom.app_smul, h2, Scheme.Modules.map_smul, presheaf_map_map_self]

/-- Restricting the value of a map into `j_*(G|_V)` commutes with restriction to a smaller open. -/
private theorem push_res_map_restrict {Y : Scheme.{u}} {V U' U : Y.Opens} {M G : Y.Modules}
    (φ : M ⟶ (push V).obj ((res V).obj G)) (h : U' ≤ U) (hU : U ≤ V) (m : Γ(M, U)) :
    G.presheaf.map (homOfLE (le_image_preimage (h.trans hU))).op
        (φ.app U' (M.presheaf.map (homOfLE h).op m)) =
      G.presheaf.map (homOfLE h).op
        (G.presheaf.map (homOfLE (le_image_preimage hU)).op (φ.app U m)) := by
  rw [hom_app_map]
  exact modules_map_map_eq G (homOfLE (interOver_mono V h))
    (homOfLE (le_image_preimage (h.trans hU))) (homOfLE (le_image_preimage hU)) (homOfLE h)
    (φ.app U m)

/-- `chartEvalSec` is `𝒪_X(U)`-linear. -/
theorem chartEvalSec_smul (U : X.Opens) (hU : U ≤ W) (r : Γ(X, U))
    (m : Γ(twistSource i c F, U)) :
    chartEvalSec F hgen U hU (r • m) = r • chartEvalSec F hgen U hU m :=
  push_res_map_smul _ (i.preimage_mono hU) ((i.app U).hom r) m

/-- `chartDescSec` is additive. -/
theorem chartDescSec_add (U : X.Opens) (hU : U ≤ W) (y y' : Γ(quotPull i F, U)) :
    chartDescSec F hgen U hU (y + y') = chartDescSec F hgen U hU y + chartDescSec F hgen U hU y' :=
  push_res_map_add _ hU y y'

/-- `chartDescSec` is `𝒪_X(U)`-linear. -/
theorem chartDescSec_smul (U : X.Opens) (hU : U ≤ W) (r : Γ(X, U)) (y : Γ(quotPull i F, U)) :
    chartDescSec F hgen U hU (r • y) = r • chartDescSec F hgen U hU y :=
  push_res_map_smul _ hU r y

/-- `chartEvalSec` commutes with restriction to a smaller open. -/
theorem chartEvalSec_restrict {U' U : X.Opens} (h : U' ≤ U) (hU : U ≤ W)
    (m : Γ(twistSource i c F, U)) :
    chartEvalSec F hgen U' (h.trans hU) ((twistSource i c F).presheaf.map (homOfLE h).op m) =
      (quotPull i F).presheaf.map (homOfLE h).op (chartEvalSec F hgen U hU m) :=
  push_res_map_restrict _ (i.preimage_mono h) (i.preimage_mono hU) m

/-- `chartDescSec` commutes with restriction to a smaller open. -/
theorem chartDescSec_restrict {U' U : X.Opens} (h : U' ≤ U) (hU : U ≤ W)
    (y : Γ(quotPull i F, U)) :
    chartDescSec F hgen U' (h.trans hU) ((quotPull i F).presheaf.map (homOfLE h).op y) =
      (supportCohomologySheaf (isClosed_chartSupport W (chartEq W f)) F (c : ℤ)).presheaf.map
        (homOfLE h).op (chartDescSec F hgen U hU y) :=
  push_res_map_restrict _ h hU y

/-- `chartSec` is additive. -/
theorem chartSec_add (U : X.Opens) (hU : U ≤ W) (m m' : Γ(twistSource i c F, U)) :
    chartSec F hgen U hU (m + m') = chartSec F hgen U hU m + chartSec F hgen U hU m' := by
  refine (chartSec_eq_iff F hgen U hU _ _).2 ?_
  rw [map_add, chartTheta_chartSec, chartTheta_chartSec, chartEvalSec_add, chartDescSec_add]

/-- `chartSec` is `𝒪_X(U)`-linear. -/
theorem chartSec_smul (U : X.Opens) (hU : U ≤ W) (r : Γ(X, U)) (m : Γ(twistSource i c F, U)) :
    chartSec F hgen U hU (r • m) = r • chartSec F hgen U hU m := by
  refine (chartSec_eq_iff F hgen U hU _ _).2 ?_
  rw [Scheme.Modules.Hom.app_smul, chartTheta_chartSec, chartEvalSec_smul, chartDescSec_smul]

/-- `chartSec` commutes with restriction to a smaller open. -/
theorem chartSec_restrict {U' U : X.Opens} (h : U' ≤ U) (hU : U ≤ W)
    (m : Γ(twistSource i c F, U)) :
    chartSec F hgen U' (h.trans hU) ((twistSource i c F).presheaf.map (homOfLE h).op m) =
      (supportCohomologySheaf (isClosed_zeroLocus i) F (c : ℤ)).presheaf.map (homOfLE h).op
        (chartSec F hgen U hU m) := by
  refine (chartSec_eq_iff F hgen U' (h.trans hU) _ _).2 ?_
  rw [hom_app_map, chartTheta_chartSec, chartEvalSec_restrict, chartDescSec_restrict]

end ChartSec

end Stacks.Perfect.ConormalClass
