module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueOfOverlapIso
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso

/-!
# The cocycle condition of a glueing datum, read on the comparison morphisms

`Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` builds a glueing datum of sheaves of
modules out of one isomorphism per pair of charts, over the overlap of the two chart images, and
asks for the cocycle condition **on sections**: for every open `V` of the base inside three chart
images, the sections maps of the `(i,j)`-th and the `(j,k)`-th comparison compose to the sections
map of the `(i,k)`-th. A construction, by contrast, produces its cocycle condition as an equality
of *morphisms of sheaves of modules*, and over the triple overlap rather than over an arbitrary
`V`. This file converts the second into the first.

## The obstruction, and what removes it

The three comparisons of one cocycle triangle live over three *different* opens of the base —
`Stacks.SheafOfModules.chartOverlap f i j`, `... f j k` and `... f i k` — so their sections maps
over `V` are taken at three different ambient opens, and `AlgebraicGeometry.localApp_comp`, which
composes two sections maps at one fixed ambient open, does not apply.

What removes the obstruction is that the sections map over `V` of a morphism of the restrictions
to `W` only depends on the restriction of that morphism to any open between the two:
`AlgebraicGeometry.localApp_restrictLocal_le` below, the generalisation of
`AlgebraicGeometry.localApp_restrictLocal` from `V = W` to an arbitrary `V ≤ W`. Restricting the
three comparisons to a common open inside all three overlaps therefore rewrites all three
sections maps at one ambient open, where `AlgebraicGeometry.localApp_comp` does apply.

## Main results

* `AlgebraicGeometry.localApp_restrictLocal_le`: **the sections map over `V' ≤ V ≤ W` of a
  morphism of the restrictions to `W` is the sections map of its restriction to `V`.**
* `AlgebraicGeometry.localApp_eq_of_restrictLocal_eq` and
  `AlgebraicGeometry.localAppFun_eq_of_restrictLocal_eq`: **the sections map does not depend on
  the ambient open** — two morphisms of restrictions to two opens containing `V` have the same
  sections map over `V` as soon as their restrictions to a common open agree.
* `AlgebraicGeometry.localApp_comp_of_restrictLocal_comp` and
  `AlgebraicGeometry.localAppFun_comp_of_restrictLocal_comp`: **sections maps taken at three
  different ambient opens compose as soon as the restrictions of the three morphisms to a common
  open compose.**
* `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso_cocycle_of_restrictLocal`: **the cocycle
  hypothesis of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` follows from the equality of
  morphisms over the triple overlap.**
* `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle`: **the glueing datum of a family
  of sheaves of modules on the charts together with isomorphisms of their pushforwards over the
  pairwise overlaps whose restrictions to the triple overlaps compose.**

## Implementation notes

`AlgebraicGeometry.restrictLocal` is multiplicative and unital at a fixed ambient open,
`AlgebraicGeometry.restrictLocal_comp` and `AlgebraicGeometry.restrictLocal_id` (both from
`StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso`); those are how
a cocycle for the comparisons themselves is turned into the hypothesis of
`ofOverlapIsoOfCocycle`.

No transport along an equality of opens appears anywhere: the ambient open is recorded in the
*type* of the argument of `AlgebraicGeometry.localApp` and the bound `V ≤ W` is a separate
hypothesis, so changing the ambient open changes only a proof.

## No tag is claimed

Stacks 00AM is carried by `Stacks.SheafOfModules.ModulesGlueData.glued` and
`...ModulesGlueData.chartIso`; this file only changes the shape in which the cocycle condition of
a datum is presented.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {A B C : X.Modules}

/-- **The sections map over an open contained in `V` of a morphism of the restrictions to `W` is
the sections map of its restriction to `V`.** This is
`AlgebraicGeometry.localApp_restrictLocal`, which is the case `V' = V`, for an arbitrary
`V' ≤ V ≤ W`; it is what makes the sections map independent of the ambient open. -/
lemma localApp_restrictLocal_le {V' V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W)
    (hV' : V' ≤ V) :
    localApp φ V' (hV'.trans hV) = localApp (restrictLocal φ hV) V' hV' := by
  have himg : W.ι ''ᵁ (X.homOfLE hV ''ᵁ (V.ι ⁻¹ᵁ V')) = V.ι ''ᵁ (V.ι ⁻¹ᵁ V') := by
    rw [← Scheme.Hom.comp_image]
    simp only [Scheme.homOfLE_ι]
  rw [localApp, localApp, restrictLocal_app φ hV (V.ι ⁻¹ᵁ V') (eqToHom himg).op
    (eqToHom himg.symm).op]
  have hU : W.ι ⁻¹ᵁ V' = X.homOfLE hV ''ᵁ (V.ι ⁻¹ᵁ V') :=
    Scheme.Hom.image_injective W.ι (by
      show W.ι ''ᵁ (W.ι ⁻¹ᵁ V') = W.ι ''ᵁ (X.homOfLE hV ''ᵁ (V.ι ⁻¹ᵁ V'))
      rw [himg, Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le (hV'.trans hV),
        Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le hV'])
  exact (conj_app_eq₃ φ (homOfLE (le_of_eq hU)) _ _ _ _ _ _).symm

/-- `AlgebraicGeometry.localAppFun` over an open contained in `V` is the one of the restriction
to `V`. -/
lemma localAppFun_restrictLocal_le {V' V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W)
    (hV' : V' ≤ V) (s : ToType (A.val.obj (op V'))) :
    localAppFun φ V' (hV'.trans hV) s = localAppFun (restrictLocal φ hV) V' hV' s :=
  ConcreteCategory.congr_hom (localApp_restrictLocal_le φ hV hV') s

/-- **The sections map does not depend on the ambient open.** Two morphisms of the restrictions
to two opens `W₁` and `W₂`, both containing an open `W`, have the same sections map over every
`V ≤ W` as soon as their restrictions to `W` agree. -/
lemma localApp_eq_of_restrictLocal_eq {V W W₁ W₂ : X.Opens}
    (φ : Scheme.Modules.restrict A W₁.ι ⟶ Scheme.Modules.restrict B W₁.ι)
    (ψ : Scheme.Modules.restrict A W₂.ι ⟶ Scheme.Modules.restrict B W₂.ι)
    (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (h : restrictLocal φ h₁ = restrictLocal ψ h₂) (hV : V ≤ W) :
    localApp φ V (hV.trans h₁) = localApp ψ V (hV.trans h₂) := by
  rw [localApp_restrictLocal_le φ h₁ hV, localApp_restrictLocal_le ψ h₂ hV, h]

/-- **`AlgebraicGeometry.localAppFun` does not depend on the ambient open.** -/
lemma localAppFun_eq_of_restrictLocal_eq {V W W₁ W₂ : X.Opens}
    (φ : Scheme.Modules.restrict A W₁.ι ⟶ Scheme.Modules.restrict B W₁.ι)
    (ψ : Scheme.Modules.restrict A W₂.ι ⟶ Scheme.Modules.restrict B W₂.ι)
    (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (h : restrictLocal φ h₁ = restrictLocal ψ h₂) (hV : V ≤ W)
    (s : ToType (A.val.obj (op V))) :
    localAppFun φ V (hV.trans h₁) s = localAppFun ψ V (hV.trans h₂) s :=
  ConcreteCategory.congr_hom (localApp_eq_of_restrictLocal_eq φ ψ h₁ h₂ h hV) s

/-- **Sections maps taken at three different ambient opens compose.** Let `φ`, `ψ` and `χ` be
morphisms of the restrictions to three opens `W₁`, `W₂` and `W₃` of the base, each containing an
open `W`, and suppose the restrictions of the three to `W` compose. Then their sections maps over
every `V ≤ W` compose, even though the three are taken at three different ambient opens.

This is the step `AlgebraicGeometry.localApp_comp` cannot take: it composes two sections maps at
one *fixed* ambient open, and the three comparisons of a cocycle triangle of a glueing datum live
over three different overlaps. -/
lemma localApp_comp_of_restrictLocal_comp {V W W₁ W₂ W₃ : X.Opens}
    (φ : Scheme.Modules.restrict A W₁.ι ⟶ Scheme.Modules.restrict B W₁.ι)
    (ψ : Scheme.Modules.restrict B W₂.ι ⟶ Scheme.Modules.restrict C W₂.ι)
    (χ : Scheme.Modules.restrict A W₃.ι ⟶ Scheme.Modules.restrict C W₃.ι)
    (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (h₃ : W ≤ W₃)
    (hcoc : restrictLocal φ h₁ ≫ restrictLocal ψ h₂ = restrictLocal χ h₃) (hV : V ≤ W) :
    localApp φ V (hV.trans h₁) ≫ localApp ψ V (hV.trans h₂) = localApp χ V (hV.trans h₃) := by
  rw [localApp_restrictLocal_le φ h₁ hV, localApp_restrictLocal_le ψ h₂ hV,
    localApp_restrictLocal_le χ h₃ hV, ← localApp_comp, hcoc]

/-- **`AlgebraicGeometry.localAppFun` taken at three different ambient opens composes**, as soon
as the restrictions of the three morphisms to a common open compose. This is the form in which
the cocycle condition of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` is asked for. -/
lemma localAppFun_comp_of_restrictLocal_comp {V W W₁ W₂ W₃ : X.Opens}
    (φ : Scheme.Modules.restrict A W₁.ι ⟶ Scheme.Modules.restrict B W₁.ι)
    (ψ : Scheme.Modules.restrict B W₂.ι ⟶ Scheme.Modules.restrict C W₂.ι)
    (χ : Scheme.Modules.restrict A W₃.ι ⟶ Scheme.Modules.restrict C W₃.ι)
    (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (h₃ : W ≤ W₃)
    (hcoc : restrictLocal φ h₁ ≫ restrictLocal ψ h₂ = restrictLocal χ h₃) (hV : V ≤ W)
    (s : ToType (A.val.obj (op V))) :
    localAppFun ψ V (hV.trans h₂) (localAppFun φ V (hV.trans h₁) s) =
      localAppFun χ V (hV.trans h₃) s :=
  congrFun (congrArg (fun g ↦ (ConcreteCategory.hom g : _ → _))
    (localApp_comp_of_restrictLocal_comp φ ψ χ h₁ h₂ h₃ hcoc hV)) s

/-! `AlgebraicGeometry.restrictLocal_comp` and `AlgebraicGeometry.restrictLocal_id`, the
multiplicativity and unitality of `AlgebraicGeometry.restrictLocal`, are the ones of
`StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso`; the unit law is a `simp` lemma
from here on, as it was when this file carried its own copy. -/

attribute [simp] restrictLocal_id

end AlgebraicGeometry

namespace Stacks.SheafOfModules

variable {S : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
  [∀ i, IsOpenImmersion (f i)]

/-- The overlap of the images of the `i`-th, the `j`-th and the `k`-th chart, as an open of the
base. This is the open over which the cocycle condition of a glueing datum lives. -/
abbrev chartTripleOverlap (i j k : ι) : S.Opens := chartOverlap f i j ⊓ (f k).opensRange

/-- The triple overlap is inside the overlap of the first two chart images. -/
lemma chartTripleOverlap_le_fst (i j k : ι) :
    chartTripleOverlap f i j k ≤ chartOverlap f i j := inf_le_left

/-- The triple overlap is inside the overlap of the last two chart images. -/
lemma chartTripleOverlap_le_snd (i j k : ι) :
    chartTripleOverlap f i j k ≤ chartOverlap f j k :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- The triple overlap is inside the overlap of the first and the last chart image. -/
lemma chartTripleOverlap_le_out (i j k : ι) :
    chartTripleOverlap f i j k ≤ chartOverlap f i k :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

variable (mod : ∀ i, (Y i).Modules)

namespace ModulesGlueData

/-- **The cocycle condition on sections follows from the cocycle condition over the triple
overlap.** The hypothesis of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` quantifies over
every open of the base inside three chart images; it is enough to know, for each triple of
charts, that the restrictions of the three comparisons to the overlap of the three chart images
compose. -/
theorem ofOverlapIso_cocycle_of_restrictLocal
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (hcoc : ∀ i j k : ι,
      restrictLocal (e i j).hom (chartTripleOverlap_le_fst f i j k) ≫
          restrictLocal (e j k).hom (chartTripleOverlap_le_snd f i j k) =
        restrictLocal (e i k).hom (chartTripleOverlap_le_out f i j k))
    (i j k : ι) (V : S.Opens) (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (hk : V ≤ (f k).opensRange) (s : ToType (openSections (f i) (mod i) V)) :
    localAppFun (e j k).hom V (le_inf hj hk) (localAppFun (e i j).hom V (le_inf hi hj) s) =
      localAppFun (e i k).hom V (le_inf hi hk) s :=
  localAppFun_comp_of_restrictLocal_comp (e i j).hom (e j k).hom (e i k).hom
    (chartTripleOverlap_le_fst f i j k) (chartTripleOverlap_le_snd f i j k)
    (chartTripleOverlap_le_out f i j k) (hcoc i j k) (le_inf (le_inf hi hj) hk) s

/-- **A glueing datum of sheaves of modules from isomorphisms over the pairwise overlaps whose
restrictions to the triple overlaps compose.** This is
`Stacks.SheafOfModules.ModulesGlueData.ofOverlapIso` with its cocycle condition in the shape a
construction produces it: an equality of morphisms of sheaves of modules over the overlap of
three chart images, one for each triple of charts, rather than an equality of maps on sections
over every open of the base inside three chart images. -/
def ofOverlapIsoOfCocycle
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (hcoc : ∀ i j k : ι,
      restrictLocal (e i j).hom (chartTripleOverlap_le_fst f i j k) ≫
          restrictLocal (e j k).hom (chartTripleOverlap_le_snd f i j k) =
        restrictLocal (e i k).hom (chartTripleOverlap_le_out f i j k)) :
    ModulesGlueData S f :=
  ofOverlapIso f mod e (ofOverlapIso_cocycle_of_restrictLocal f mod e hcoc)

/-- The charts of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle` are the given
modules. -/
@[simp] theorem ofOverlapIsoOfCocycle_mod
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (hcoc : ∀ i j k : ι,
      restrictLocal (e i j).hom (chartTripleOverlap_le_fst f i j k) ≫
          restrictLocal (e j k).hom (chartTripleOverlap_le_snd f i j k) =
        restrictLocal (e i k).hom (chartTripleOverlap_le_out f i j k)) :
    (ofOverlapIsoOfCocycle f mod e hcoc).mod = mod := rfl

/-- The transition of `Stacks.SheafOfModules.ModulesGlueData.ofOverlapIsoOfCocycle` is the
sections map of the given isomorphism. -/
@[simp] theorem ofOverlapIsoOfCocycle_trans
    (e : ∀ i j : ι, Scheme.Modules.restrict (pushforwardChart f mod i) (chartOverlap f i j).ι ≅
      Scheme.Modules.restrict (pushforwardChart f mod j) (chartOverlap f i j).ι)
    (hcoc : ∀ i j k : ι,
      restrictLocal (e i j).hom (chartTripleOverlap_le_fst f i j k) ≫
          restrictLocal (e j k).hom (chartTripleOverlap_le_snd f i j k) =
        restrictLocal (e i k).hom (chartTripleOverlap_le_out f i j k))
    (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (s : ToType (openSections (f i) (mod i) V)) :
    (ofOverlapIsoOfCocycle f mod e hcoc).trans i j hi hj s =
      localAppFun (e i j).hom V (le_inf hi hj) s := rfl

end ModulesGlueData

end Stacks.SheafOfModules

end
