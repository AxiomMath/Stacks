module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ExistsRegularSection
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.RegularOnComponents
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalkBasisGenericPoint
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Regularity of the pullback of a regular meromorphic section

Let `f : X ⟶ Y` be a morphism for which pullbacks of meromorphic functions are defined
(Definition [Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)) and let `L` be an invertible
`𝒪_Y`-module. Part (1) of [Tag 02OY](https://stacks.math.columbia.edu/tag/02OY) constructs the
pullback `f^* s` of a meromorphic section `s` of `L`; if `s` is *regular*, so is `f^* s`. That
is part (2) of the tag, proved in its stated generality by
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible`.
This file proves the case of an integral source by a shorter argument at the generic point,
which is the form the Chow development consumes.

## Main results

* `AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection`: the regularity of
  the pullback for a morphism of schemes whose source is integral and whose generic point is
  carried to a generic point of an irreducible component of the target.
* `Stacks.Chow.isRegularMeromorphicSection_pullbackMeromorphicSection_subschemeι`: the instance
  at the inclusion of an irreducible component carrying an integral closed subscheme structure,
  which is part (3) of [Tag 02SW](https://stacks.math.columbia.edu/tag/02SW).
* `AlgebraicGeometry.meromorphicSectionSheafPullback_app_toMeromorphicSectionSheafAsModule` and
  `AlgebraicGeometry.pullbackMeromorphicSection_val_map_obj`: the two evaluation lemmas for the
  pullback morphism of Tag 02OY part (1), which had none.

## Implementation notes

**The hypotheses are stronger than the source's**, which states part (2) for an arbitrary
morphism of locally ringed spaces satisfying Tag 02OT and omits the proof. What is proved here
is the case of a morphism of *schemes* `f : X ⟶ Y` with `X` integral and `f` carrying the
generic point of `X` to a generic point of an irreducible component of `Y` — case (3) of
[Tag 02OU](https://stacks.math.columbia.edu/tag/02OU), and in particular the inclusion of an
irreducible component. Those hypotheses make the generic-point argument below available, which
is shorter than the general one: the general case runs at every point of `X`, from the normal
form of `f^* s` rather than from its germ at one point, and is
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible`.

The argument is the one the source's "Omitted" hides, read at the generic point. On an integral
scheme a meromorphic section whose germs never vanish is regular
(`Stacks.ChernCap42.isRegularMeromorphicSection_of_germ_ne_zero`, which needs no invertibility)
and a germ nonzero at the generic point is nonzero everywhere
(`Stacks.ChernCap42.germ_ne_zero_of_germ_genericPoint_ne_zero`). So only the germ of `f^* s` at
the generic point `ξ` of `X` has to be shown nonzero, and three steps do it.

*The value of `f^* s` near `ξ`.* The only handle on the pullback morphism
`𝒦_Y(L) ⟶ f_* 𝒦_X(f^* L)` was the adjunction identity
`AlgebraicGeometry.unit_comp_meromorphicSectionSheafPullback`. Evaluating it at an open set and
a section gives `meromorphicSectionSheafPullback_app_toMeromorphicSectionSheafAsModule`: the
pullback carries the meromorphic image of an honest section `t` of `L` over `V` to the
meromorphic image of the pullback of `t` over `f^{-1} V`. Reading a global section of a direct
image over a preimage is `pullbackMeromorphicSection_val_map_obj`, which is the compatibility of
the family `AlgebraicGeometry.pullbackMeromorphicSection` is assembled from.

*Near a generic point `s` is an honest section with a basis germ.* This is
`AlgebraicGeometry.exists_isStalkBasis_toMeromorphicSectionSheafAsModule_eq`, and it is the one
place regularity of `s` is used.

*The germ of a pullback.* Tag 0098,
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, identifies
`(f^* L)_ξ` with `𝒪_{X, ξ} ⊗_{𝒪_{Y, y}} L_y` carrying the germ of the pullback of `t` to
`1 ⊗ germ t`; a pure tensor on a basis is nonzero after any base change to a nontrivial ring,
which is the private `one_tmul_ne_zero_of_bijective_smul`. The stalk-of-pullback comparison is
therefore available: it is proved, in existential form, and phrased exactly at the unit of
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` that the pullback of
meromorphic sections is built from, so nothing has to be transported.

Finally `Stacks.ChernCap42.injective_toMeromorphicSectionStalk` turns a nonzero germ of `f^* t`
into a nonzero germ of its meromorphic image; the invertibility of `f^* L` that it needs is
`RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme`.

## References

* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TensorProduct

universe u

/-- A pure tensor `1 ⊗ m` on a basis `m` of a free rank one module is nonzero after base change
to a nontrivial ring: `B ⊗_A M` is `B ⊗_A A`, which is `B`, and `1 ⊗ m` goes to `1`. -/
private theorem one_tmul_ne_zero_of_bijective_smul {R A M : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Nontrivial A] [AddCommGroup M] [Module R M] {m : M}
    (hm : Function.Bijective fun c : R => c • m) : (1 : A) ⊗ₜ[R] m ≠ 0 := by
  let e : R ≃ₗ[R] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M m) hm
  have hem : e.symm m = 1 := e.symm_apply_eq.2 (one_smul R m).symm
  intro h
  have h2 : (TensorProduct.rid R A) ((TensorProduct.congr (LinearEquiv.refl R A) e.symm)
      ((1 : A) ⊗ₜ[R] m)) = 0 := by rw [h, map_zero, map_zero]
  rw [TensorProduct.congr_tmul, hem] at h2
  simp only [LinearEquiv.refl_apply, TensorProduct.rid_tmul, one_smul] at h2
  exact one_ne_zero h2

namespace AlgebraicGeometry

/-! ### Evaluating the pullback of meromorphic sections -/

/-- **The pullback morphism on sheaves of meromorphic sections, evaluated on the meromorphic
image of an honest section.** The meromorphic image over `V` of a section `t` of `F` is carried
to the meromorphic image over `f^{-1} V` of the pullback of `t`.

This is `AlgebraicGeometry.unit_comp_meromorphicSectionSheafPullback` read at an open set and a
section; by the adjunction that property determines
`AlgebraicGeometry.meromorphicSectionSheafPullback` completely. -/
theorem meromorphicSectionSheafPullback_app_toMeromorphicSectionSheafAsModule
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : PullbacksMeromorphicSections f.toLRSHom)
    (F : Y.Modules) (V : Y.Opens) (t : F.val.obj (op V)) :
    ((meromorphicSectionSheafPullback f.toLRSHom hf F).val.app (op V)).hom
        (((toMeromorphicSectionSheafAsModule Y F).val.app (op V)).hom t) =
      ((toMeromorphicSectionSheafAsModule X
        ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj F)).val.app
          (op ((Opens.map f.base).obj V))).hom
        ((((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          f.toLRSHom.toShHom).unit.app F).val.app (op V)).hom t) :=
  congrArg (fun φ => ((SheafOfModules.Hom.val φ).app (op V)).hom t)
    (unit_comp_meromorphicSectionSheafPullback f.toLRSHom hf F)

/-- **The pullback of a meromorphic section, read over the preimage of an open set.** Its value
there is the value of the pullback morphism at that open set; this is the compatibility of the
family of values that `AlgebraicGeometry.pullbackMeromorphicSection` is assembled from. -/
theorem pullbackMeromorphicSection_val_map_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : PullbacksMeromorphicSections f.toLRSHom) (F : Y.Modules)
    (s : MeromorphicSection Y.sheaf F) (V : Y.Opens) :
    (pullbackMeromorphicSection f.toLRSHom hf F s).val (op ((Opens.map f.base).obj V)) =
      ((meromorphicSectionSheafPullback f.toLRSHom hf F).val.app (op V)).hom (s.val (op V)) :=
  PresheafOfModules.sections_property
    (SheafOfModules.sectionsMap (meromorphicSectionSheafPullback f.toLRSHom hf F) s)
    (homOfLE (le_top (a := V))).op

/-! ### Germs of a meromorphic section -/

/-- **A meromorphic section with a nonzero germ over some open set has a nonzero germ over the
whole space.** Its value over the whole space restricts to its value over the open set, and
restricting a section does not change its germ. -/
private theorem germ_top_ne_zero_of_germ_ne_zero {X : Scheme.{u}} (N : X.Modules)
    (σ : MeromorphicSection X.sheaf N) {U : X.Opens} {x : X} (hxU : x ∈ U)
    (h : Stacks.ModuleStalk.germ (meromorphicSectionSheaf X.sheaf N).val U x hxU
      (σ.val (op U)) ≠ 0) :
    Stacks.ModuleStalk.germ (meromorphicSectionSheaf X.sheaf N).val ⊤ x trivial
      (σ.val (op ⊤)) ≠ 0 := by
  intro h0
  refine h ?_
  have hres : Stacks.ModuleStalk.res (meromorphicSectionSheaf X.sheaf N).val
      (le_top (a := U)) (σ.val (op ⊤)) = σ.val (op U) :=
    PresheafOfModules.sections_property σ (homOfLE (le_top (a := U))).op
  have hgerm := Stacks.ModuleStalk.germ_res (meromorphicSectionSheaf X.sheaf N).val
    (le_top (a := U)) hxU (σ.val (op ⊤))
  rw [hres] at hgerm
  exact hgerm.trans h0

/-- **The meromorphic image of a section of an invertible module has a nonzero germ whenever the
section does.** The stalk of an invertible module embeds in the stalk of its sheaf of meromorphic
sections, `Stacks.ChernCap42.injective_toMeromorphicSectionStalk`. -/
private theorem germ_toMeromorphicSectionSheafAsModule_ne_zero {X : Scheme.{u}} (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    {U : X.Opens} {x : X} (hxU : x ∈ U) (n : N.val.obj (op U))
    (hn : Stacks.ModuleStalk.germ N.val U x hxU n ≠ 0) :
    Stacks.ModuleStalk.germ (meromorphicSectionSheaf X.sheaf N).val U x hxU
      (((toMeromorphicSectionSheafAsModule X N).val.app (op U)).hom n) ≠ 0 := by
  intro h0
  refine hn (Stacks.ChernCap42.injective_toMeromorphicSectionStalk N x ?_)
  rw [map_zero]
  exact (Stacks.ModuleStalk.stalkMap_germ
    (Stacks.Divisors.toMeromorphicSectionSheaf X.sheaf N) x U hxU n).trans h0

/-! ### Tag 02OY part (2) -/

/-- **The pullback of a regular meromorphic section is regular, for an integral source.** Let
`f : X ⟶ Y` be a morphism of schemes for which pullbacks of meromorphic functions are defined,
with `X` integral and the generic point of `X` carried to a generic point of an irreducible
component of `Y`, let `L` be an invertible `𝒪_Y`-module and let `s` be a regular meromorphic
section of `L`. Then the pullback `f^* s` of Tag 02OY part (1) is a regular meromorphic section
of `f^* L`.

This is Tag 02OY part (2) under two extra hypotheses, which is case (3) of Tag 02OU and the
configuration the Chow development uses; the tag itself, for an arbitrary morphism of locally
ringed spaces, is
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection_of_isInvertible`.

Under those hypotheses regularity is a condition at the generic point `ξ` of `X` alone. Near its
image `s` is the meromorphic image of a section `t` of `L` whose germ is a stalk basis; the
pullback morphism carries that meromorphic image to the meromorphic image of the pullback of `t`;
the germ of that pullback at `ξ` is the pure tensor `1 ⊗ germ t` of Tag 0098, nonzero on a basis;
and the stalk of `f^* L` embeds in the stalk of its sheaf of meromorphic sections because
`f^* L` is invertible. -/
theorem isRegularMeromorphicSection_pullbackMeromorphicSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] (hf : PullbacksMeromorphicSections f.toLRSHom)
    (hfη : f.base (genericPoint X) ∈ genericPoints Y) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L)
    (s : MeromorphicSection Y.sheaf L) (hs : IsRegularMeromorphicSection Y.sheaf L s) :
    IsRegularMeromorphicSection X.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L)
      (pullbackMeromorphicSection f.toLRSHom hf L s) := by
  have hLinst : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L := hL
  have hNinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme f L
  refine Stacks.ChernCap42.isRegularMeromorphicSection_of_germ_ne_zero X
    ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L)
    (pullbackMeromorphicSection f.toLRSHom hf L s) fun x =>
    Stacks.ChernCap42.germ_ne_zero_of_germ_genericPoint_ne_zero _ _ x ?_
  -- a local description of `s` near the image of the generic point of `X`
  obtain ⟨V, hyV, t, hts, hbasis⟩ :=
    exists_isStalkBasis_toMeromorphicSectionSheafAsModule_eq Y L hL s hs hfη
  -- the value of `f^* s` over `f⁻¹ V` is the meromorphic image of the pullback of `t`
  have hσU : (pullbackMeromorphicSection f.toLRSHom hf L s).val
        (op ((Opens.map f.base).obj V)) =
      ((toMeromorphicSectionSheafAsModule X
        ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L)).val.app
          (op ((Opens.map f.base).obj V))).hom
        ((((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
          f.toLRSHom.toShHom).unit.app L).val.app (op V)).hom t) := by
    rw [pullbackMeromorphicSection_val_map_obj f hf L s V, ← hts,
      meromorphicSectionSheafPullback_app_toMeromorphicSectionSheafAsModule f hf L V t]
  -- the germ of the pullback of `t` at the generic point is nonzero
  have hgermn : Stacks.ModuleStalk.germ (O := X.sheaf.presheaf)
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj L).val
        ((Opens.map f.base).obj V) (genericPoint X) hyV
          ((((RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction
            f.toLRSHom.toShHom).unit.app L).val.app (op V)).hom t) ≠ 0 := by
    let _ : Algebra (Y.presheaf.stalk (f.base (genericPoint X)))
        (X.presheaf.stalk (genericPoint X)) :=
      (f.toLRSHom.toShHom.hom.stalkMap (genericPoint X)).hom.toAlgebra
    obtain ⟨e, he⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom L (genericPoint X)
    exact fun h0 => one_tmul_ne_zero_of_bijective_smul (A := X.presheaf.stalk (genericPoint X))
      hbasis (((he V hyV t).symm.trans (congrArg e h0)).trans (map_zero e))
  -- hence so is the germ of its meromorphic image, and so is the germ of `f^* s`
  refine germ_top_ne_zero_of_germ_ne_zero _ (pullbackMeromorphicSection f.toLRSHom hf L s)
    (U := (Opens.map f.base).obj V) (x := genericPoint X) hyV ?_
  rw [hσU]
  exact germ_toMeromorphicSectionSheafAsModule_ne_zero _
    (U := (Opens.map f.base).obj V) (x := genericPoint X) hyV _ hgermn

end AlgebraicGeometry

namespace Stacks.Chow

/-- **The restriction of a regular meromorphic section to an irreducible component is regular.**
Let `W : X.IdealSheafData` present an irreducible component of `X` with an integral closed
subscheme structure, let `L` be an invertible `𝒪_X`-module and let `s` be a regular meromorphic
section of `L`. Then the pullback of `s` along the inclusion of that subscheme — which exists by
Tag 02OU, `Stacks.Chow.pullbacksMeromorphicSections_subschemeι` — is a regular meromorphic
section of the restriction of `L`.

Together with the existence of the pullback this is part (3) of
[Tag 02SW](https://stacks.math.columbia.edu/tag/02SW), stated for every irreducible component
rather than only for those of delta-dimension `k + 1`; the whole of that tag is
`Stacks.Chow.denominatorQuotients_shortExact_isCoherent_and_firstChernClassCap`. The proof is the
instance at a closed immersion of
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection`, which is itself a
special case of part (2) of Tag 02OY. -/
theorem isRegularMeromorphicSection_pullbackMeromorphicSection_subschemeι {X : Scheme.{u}}
    (W : X.IdealSheafData) [IsIntegral W.subscheme]
    (hW : (W.support : Set X) ∈ irreducibleComponents X) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsRegularMeromorphicSection W.subscheme.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback W.subschemeι.toLRSHom.toShHom).obj L)
      (pullbackMeromorphicSection W.subschemeι.toLRSHom
        (pullbacksMeromorphicSections_subschemeι W hW) L s) :=
  isRegularMeromorphicSection_pullbackMeromorphicSection W.subschemeι
    (pullbacksMeromorphicSections_subschemeι W hW)
    (subschemeι_genericPoint_mem_genericPoints W hW) L hL s hs

end Stacks.Chow

end
