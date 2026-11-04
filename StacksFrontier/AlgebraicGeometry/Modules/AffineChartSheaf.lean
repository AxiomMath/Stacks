module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The sheaf of modules determined by a module over an affine chart

Let `Y` be a scheme, let `V ⊆ Y` be an affine open and write `R := Γ(Y, V)`. Every `R`-module
`M` determines a sheaf of `𝒪_Y`-modules, namely the pushforward of Serre's sheaf `M^~` on
`Spec R` along the canonical open immersion `IsAffineOpen.fromSpec : Spec Γ(Y, V) ⟶ Y`. This
file constructs that sheaf and records the two properties that make it usable as a *chart* for
a quasi-coherent sheaf: its sections over `V` are `M` itself, and its sections over a basic
open `D(g)` of `V` are the localization `M[1/g]`.

## Main definitions

* `Stacks.Modules.chartSheaf`: the sheaf `(fromSpec)_* M^~` of `𝒪_Y`-modules.
* `Stacks.Modules.chartSection`: the canonical map from `M` to the sections of `chartSheaf`
  over an arbitrary open of `Y`.
* `Stacks.Modules.chartTopEquiv`: the `Γ(Y, V)`-linear equivalence `M ≃ Γ(chartSheaf, V)`.
* `Stacks.Modules.chartSectionBasicOpen` and `Stacks.Modules.chartRestrictBasicOpen`: the
  previous maps packaged as `Γ(Y, V)`-linear maps into the sections over a basic open `D(g)`,
  the second one being the restriction map of the sheaf.
* `Stacks.Modules.pushforwardEquiv` and `Stacks.Modules.pushforwardInvIsoPullback`: pushforward
  of modules along an isomorphism of schemes is an equivalence, and pushing forward along the
  inverse is pulling back along the isomorphism.
* `Stacks.Modules.restrictChartSheafIso`: the restriction of `chartSheaf V M` to the open
  subscheme `V` is the pullback of `M^~` along `V ≅ Spec Γ(Y, V)`.

## Main results

* `Stacks.Modules.chartSection_smul`: the scalar bridge. The `Γ(Y, V)`-module structure that
  `M^~` puts on the sections of `chartSheaf` over `W ⊆ V` agrees with the one coming from the
  sheaf of modules structure along `Γ(Y, V) ⟶ Γ(Y, W)`.
* `Stacks.Modules.isLocalizedModule_chartSectionBasicOpen` and
  `Stacks.Modules.isLocalizedModule_chartRestrictBasicOpen`: for `g : Γ(Y, V)` the sections of
  `chartSheaf` over `Y.basicOpen g` are the localization of `M` away from `g`; equivalently the
  sheaf restriction `Γ(chartSheaf, V) ⟶ Γ(chartSheaf, Y.basicOpen g)` is a localization map
  once `Γ(chartSheaf, V)` is identified with `M` via `chartTopEquiv`.
* `Stacks.Modules.isQuasicoherent_restrict_chartSheaf`: the restriction of `chartSheaf V M` to
  the open subscheme `V` is quasi-coherent.

## Implementation notes

The sections `Γ(chartSheaf V M, W)` are *definitionally* the sections of `M^~` over
`fromSpec ⁻¹ᵁ W`, because `AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj` holds by
`rfl`. This is what lets `chartSection` be defined without transporting data along an equality
of opens, and it makes compatibility with restriction (`chartSection_res`) a `rfl`.

The two `Γ(Y, V)`-module structures on `Γ(chartSheaf V M, W)` for `W ≤ V` — the one from
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, where `Γ(M^~, U)` is an `R`-module for every
`U`, and the one obtained from the sheaf of modules structure by restricting scalars along
`Γ(Y, V) ⟶ Γ(Y, W)` — are *not* definitionally equal: comparing them amounts to the identity
`fromSpec.app W ∘ Γ(Y, V ⊆ W) = Γ(Spec R, ⊤ ⊆ fromSpec ⁻¹ᵁ W) ∘ (ΓSpecIso R).inv`, proved in
`presheaf_map_comp_fromSpec_app` from naturality of `Scheme.Hom.app` and
`IsAffineOpen.fromSpec_app_self`. Everything downstream is stated for the sheaf structure,
which is the one a user of `chartSheaf` meets; `chartSection_smul` is the bridge. The restricted
scalar structure is only registered as an instance in the case `W = Y.basicOpen g` that is
actually used, as `moduleSectionsBasicOpen`; for a general `W ≤ V` there is no canonical choice
of the inclusion, so no instance can be declared.

Bijectivity statements are proved by rewriting the open inside the (propositional) goal — e.g.
`fromSpec ⁻¹ᵁ V = ⊤` turns `IsIso (tilde.toOpen M (fromSpec ⁻¹ᵁ V))` into the Mathlib instance
`tilde.isIso_toOpen_top` — rather than by transporting `tilde.toOpen` along that equality.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* `Mathlib/AlgebraicGeometry/Modules/Tilde.lean`, for the sheaf `M^~` on `Spec R`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Modules

/-- Pushforward of sheaves of modules along an isomorphism of schemes is an equivalence of
categories: the two composites are identified with pushforward along an identity. -/
def pushforwardEquiv {X Z : Scheme.{u}} (f : X ≅ Z) : X.Modules ≌ Z.Modules :=
  .mk (Scheme.Modules.pushforward f.hom) (Scheme.Modules.pushforward f.inv)
    (Scheme.Modules.pushforwardComp f.hom f.inv ≪≫
      Scheme.Modules.pushforwardCongr f.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm
    (Scheme.Modules.pushforwardComp f.inv f.hom ≪≫
      Scheme.Modules.pushforwardCongr f.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Z)

/-- For an isomorphism of schemes `f`, pushforward along `f.inv` is the pullback along `f.hom`:
both are left adjoint to pushforward along `f.hom`. -/
def pushforwardInvIsoPullback {X Z : Scheme.{u}} (f : X ≅ Z) :
    Scheme.Modules.pushforward f.inv ≅ Scheme.Modules.pullback f.hom :=
  (pushforwardEquiv f.symm).toAdjunction.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction f.hom)

variable {Y : Scheme.{u}} (V : Y.affineOpens) (M : ModuleCat.{u} Γ(Y, V.1)) {W W' : Y.Opens}

/-- The sheaf of `𝒪_Y`-modules determined by a module `M` over the ring of functions on an
affine open `V` of `Y`: the pushforward of `M^~` along `Spec Γ(Y, V) ⟶ Y`. -/
def chartSheaf : Y.Modules :=
  (Scheme.Modules.pushforward V.2.fromSpec).obj (AlgebraicGeometry.tilde M)

/-- The sections of `chartSheaf V M` over an open `W` of `Y` are, definitionally, the sections
of `M^~` over the preimage of `W` in `Spec Γ(Y, V)`. -/
lemma chartSheaf_presheaf_obj (W : Y.Opens) :
    Γ(chartSheaf V M, W) = Γ(AlgebraicGeometry.tilde M, V.2.fromSpec ⁻¹ᵁ W) :=
  rfl

/-- Restricting a function on `V` to a smaller open `W` and then pulling it back along
`fromSpec` is the same as pulling it back to the whole of `Spec Γ(Y, V)` and restricting there.
This is the identity underlying the scalar bridge `chartSection_smul`. -/
lemma presheaf_map_comp_fromSpec_app (hW : W ≤ V.1) :
    Y.presheaf.map (homOfLE hW).op ≫ V.2.fromSpec.app W =
      (Scheme.ΓSpecIso Γ(Y, V.1)).inv ≫
        (Spec Γ(Y, V.1)).presheaf.map (V.2.fromSpec ⁻¹ᵁ W).leTop.op := by
  rw [Scheme.Hom.naturality, V.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  congr 1

/-- The element form of `presheaf_map_comp_fromSpec_app`. -/
lemma fromSpec_app_presheaf_map (hW : W ≤ V.1) (r : Γ(Y, V.1)) :
    V.2.fromSpec.app W (Y.presheaf.map (homOfLE hW).op r) =
      (Spec Γ(Y, V.1)).presheaf.map (V.2.fromSpec ⁻¹ᵁ W).leTop.op
        ((Scheme.ΓSpecIso Γ(Y, V.1)).inv r) := by
  rw [← ConcreteCategory.comp_apply, presheaf_map_comp_fromSpec_app V hW,
    ConcreteCategory.comp_apply]

/-- The scalar bridge, on the sections of `M^~`: for `W ≤ V` and `r : Γ(Y, V)`, acting by the
restriction of `r` to `W` through the sheaf of modules structure of `chartSheaf V M` is acting
by `r` through the `Γ(Y, V)`-module structure of `Γ(M^~, fromSpec ⁻¹ᵁ W)`. -/
lemma smul_sections_tilde (hW : W ≤ V.1) (r : Γ(Y, V.1))
    (s : Γ(AlgebraicGeometry.tilde M, V.2.fromSpec ⁻¹ᵁ W)) :
    V.2.fromSpec.app W (Y.presheaf.map (homOfLE hW).op r) • s =
      (Spec Γ(Y, V.1)).presheaf.map (V.2.fromSpec ⁻¹ᵁ W).leTop.op
        ((Scheme.ΓSpecIso Γ(Y, V.1)).inv r) • s := by
  rw [fromSpec_app_presheaf_map V hW]

/-- The canonical map from `M` to the sections of `chartSheaf V M` over an open `W` of `Y`,
given by `AlgebraicGeometry.tilde.toOpen` on the preimage of `W`. -/
def chartSection (W : Y.Opens) (m : M) : Γ(chartSheaf V M, W) :=
  (tilde.toOpen M (V.2.fromSpec ⁻¹ᵁ W)).hom m

/-- `chartSection` is compatible with the restriction maps of `chartSheaf V M`. -/
lemma chartSection_res (hW : W' ≤ W) (m : M) :
    (chartSheaf V M).presheaf.map (homOfLE hW).op (chartSection V M W m) =
      chartSection V M W' m :=
  rfl

/-- `chartSection V M W` is additive. -/
lemma chartSection_add (W : Y.Opens) (m m' : M) :
    chartSection V M W (m + m') = chartSection V M W m + chartSection V M W m' :=
  map_add _ _ _

/-- `chartSection V M W` sends `0` to `0`. -/
lemma chartSection_zero (W : Y.Opens) : chartSection V M W 0 = 0 :=
  map_zero _

/-- **The scalar bridge.** For `W ≤ V`, `r : Γ(Y, V)` and `m : M`, the section determined by
`r • m` is the restriction of `r` to `W` acting, through the sheaf of modules structure of
`chartSheaf V M`, on the section determined by `m`. -/
lemma chartSection_smul (hW : W ≤ V.1) (r : Γ(Y, V.1)) (m : M) :
    chartSection V M W (r • m) = Y.presheaf.map (homOfLE hW).op r • chartSection V M W m :=
  ((tilde.toOpen M _).hom.map_smul r m).trans (smul_sections_tilde V M hW r _).symm

/-- Over `V` itself, `chartSection` is bijective: the preimage of `V` under `fromSpec` is the
whole of `Spec Γ(Y, V)`, where `tilde.toOpen` is an isomorphism. -/
lemma bijective_chartSection_self : Function.Bijective (chartSection V M V.1) := by
  have h : IsIso (tilde.toOpen M (V.2.fromSpec ⁻¹ᵁ V.1)) := by
    rw [V.2.fromSpec_preimage_self]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- The sections of `chartSheaf V M` over `V` are `M`: a `Γ(Y, V)`-linear equivalence whose
underlying function is `chartSection V M V`. -/
def chartTopEquiv : M ≃ₗ[Γ(Y, V.1)] Γ(chartSheaf V M, V.1) :=
  LinearEquiv.ofBijective
    { toFun := chartSection V M V.1
      map_add' := chartSection_add V M V.1
      map_smul' r m := by
        refine (chartSection_smul V M le_rfl r m).trans ?_
        simp }
    (bijective_chartSection_self V M)

/-- `chartTopEquiv V M` sends `m` to `chartSection V M V.1 m`. -/
@[simp]
lemma chartTopEquiv_apply (m : M) : chartTopEquiv V M m = chartSection V M V.1 m := rfl

/-- For `g : Γ(Y, V)` the sections of `chartSheaf V M` over the basic open `D(g)` form a
`Γ(Y, V)`-module, by restricting scalars along `Γ(Y, V) ⟶ Γ(Y, D(g))`. -/
instance moduleSectionsBasicOpen (g : Γ(Y, V.1)) :
    Module Γ(Y, V.1) Γ(chartSheaf V M, Y.basicOpen g) :=
  Module.compHom _ (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom

/-- `chartSection` over a basic open `D(g)` of `V`, as a `Γ(Y, V)`-linear map. -/
def chartSectionBasicOpen (g : Γ(Y, V.1)) :
    M →ₗ[Γ(Y, V.1)] Γ(chartSheaf V M, Y.basicOpen g) where
  toFun := chartSection V M (Y.basicOpen g)
  map_add' := chartSection_add V M _
  map_smul' r m := chartSection_smul V M (Y.basicOpen_le g) r m

/-- `chartSectionBasicOpen V M g` sends `m` to `chartSection V M (Y.basicOpen g) m`. -/
@[simp]
lemma chartSectionBasicOpen_apply (g : Γ(Y, V.1)) (m : M) :
    chartSectionBasicOpen V M g m = chartSection V M (Y.basicOpen g) m := rfl

/-- The restriction map of `chartSheaf V M` from `V` to a basic open `D(g)`, as a
`Γ(Y, V)`-linear map. -/
def chartRestrictBasicOpen (g : Γ(Y, V.1)) :
    Γ(chartSheaf V M, V.1) →ₗ[Γ(Y, V.1)] Γ(chartSheaf V M, Y.basicOpen g) where
  toFun := (chartSheaf V M).presheaf.map (homOfLE (Y.basicOpen_le g)).op
  map_add' := map_add _
  map_smul' r x := Scheme.Modules.map_smul _ _ r x

/-- `chartRestrictBasicOpen V M g` is the restriction map of `chartSheaf V M` from `V` to
`Y.basicOpen g`. -/
@[simp]
lemma chartRestrictBasicOpen_apply (g : Γ(Y, V.1)) (x : Γ(chartSheaf V M, V.1)) :
    chartRestrictBasicOpen V M g x =
      (chartSheaf V M).presheaf.map (homOfLE (Y.basicOpen_le g)).op x :=
  rfl

/-- **The sections over a basic open are a localization.** For `g : Γ(Y, V)` the map
`chartSectionBasicOpen V M g : M → Γ(chartSheaf V M, Y.basicOpen g)` exhibits the sections of
`chartSheaf V M` over `D(g)` as the localization of `M` away from `g`. -/
theorem isLocalizedModule_chartSectionBasicOpen (g : Γ(Y, V.1)) :
    IsLocalizedModule (Submonoid.powers g) (chartSectionBasicOpen V M g) := by
  have h₀ : IsLocalizedModule (Submonoid.powers g)
      (tilde.toOpen M (V.2.fromSpec ⁻¹ᵁ Y.basicOpen g)).hom := by
    rw [V.2.fromSpec_preimage_basicOpen]
    infer_instance
  let e : ↥((modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj
        (op (V.2.fromSpec ⁻¹ᵁ Y.basicOpen g))) ≃ₗ[Γ(Y, V.1)]
      Γ(chartSheaf V M, Y.basicOpen g) :=
    { toFun := id
      map_add' _ _ := rfl
      map_smul' r s := (smul_sections_tilde V M (Y.basicOpen_le g) r s).symm
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl }
  have he : chartSectionBasicOpen V M g =
      e ∘ₗ (tilde.toOpen M (V.2.fromSpec ⁻¹ᵁ Y.basicOpen g)).hom := by
    ext m
    rfl
  rw [he]
  exact IsLocalizedModule.of_linearEquiv _ _ e (hf := h₀)

/-- `chartSectionBasicOpen` is the sheaf restriction map composed with the identification of
`M` with the sections over `V`. -/
theorem chartSectionBasicOpen_eq_comp (g : Γ(Y, V.1)) :
    chartSectionBasicOpen V M g =
      chartRestrictBasicOpen V M g ∘ₗ (chartTopEquiv V M : M →ₗ[Γ(Y, V.1)] _) := by
  ext m
  rfl

/-- **The restriction map of `chartSheaf V M` to a basic open is a localization map.** This is
`isLocalizedModule_chartSectionBasicOpen` transported along `chartTopEquiv`. -/
theorem isLocalizedModule_chartRestrictBasicOpen (g : Γ(Y, V.1)) :
    IsLocalizedModule (Submonoid.powers g) (chartRestrictBasicOpen V M g) := by
  refine (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers g)
    (chartTopEquiv V M : M →ₗ[Γ(Y, V.1)] _) (chartTopEquiv V M).bijective).mp ?_
  rw [← chartSectionBasicOpen_eq_comp]
  exact isLocalizedModule_chartSectionBasicOpen V M g

/-- Restricting `chartSheaf V M` to the open subscheme `V` gives the pullback of `M^~` along
the isomorphism `V ≅ Spec Γ(Y, V)`. Indeed `fromSpec` factors as `V.isoSpec.inv ≫ V.ι`, so
`chartSheaf V M` is a pushforward along `V.ι`, which restriction undoes. -/
def restrictChartSheafIso :
    (chartSheaf V M).restrict V.1.ι ≅
      (Scheme.Modules.pullback V.2.isoSpec.hom).obj (AlgebraicGeometry.tilde M) :=
  (Scheme.Modules.restrictFunctor V.1.ι).mapIso
      ((Scheme.Modules.pushforwardComp V.2.isoSpec.inv V.1.ι).app _).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso V.1.ι).app _ ≪≫
    (pushforwardInvIsoPullback V.2.isoSpec).app (AlgebraicGeometry.tilde M)

/-- **`chartSheaf V M` is quasi-coherent on `V`.** Its restriction to the open subscheme `V` is
a pullback of `M^~`, hence quasi-coherent by `Stacks.Modules.isQuasicoherent_pullback`. -/
theorem isQuasicoherent_restrict_chartSheaf :
    ((chartSheaf V M).restrict V.1.ι).IsQuasicoherent := by
  have h : ((Scheme.Modules.pullback V.2.isoSpec.hom).obj
      (AlgebraicGeometry.tilde M)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent V.1.toScheme.ringCatSheaf).prop_of_iso
    (restrictChartSheafIso V M).symm h

end Stacks.Modules

end
