module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdeal
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions

/-!
# The infinitesimal tower of a fibre, read on the base change to the local ring

`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalBaseIdeal.lean` identifies the
`n`-th infinitesimal neighbourhood `X_n` of the fibre of `f : X ⟶ Y` over `y` with the closed
subscheme of `X' = X ×_Y Spec 𝒪_{Y,y}` cut out by `(𝔪_y 𝒪_{X'}) ^ n`. This file reads that
identification on global functions, which is the form the theorem on formal functions needs.

The point is that the canonical restriction map
`Stacks.FormalFunctions.infinitesimalStalkRestrict`, which goes from the stalk `(f_* 𝒪_X)_y` to
`Γ(X_n, 𝒪)`, **factors through the global functions on `X'`**: a function on `f ⁻¹ U` restricts
to `X_n` by first pulling back to `X'` — legitimate because `X'` lies over every open
neighbourhood of `y` — and then restricting along the closed immersion `X_n ⟶ X'`. So the whole
tower `n ↦ Γ(X_n, 𝒪)` with its maps out of the stalk is the tower of the ideal-power quotients
of `𝒪_{X'}` with its maps out of `Γ(X', 𝒪_{X'})`, which is what [Stacks, Tag 02OB] and
[Stacks, Tag 02OC] are stated for over the affine base `Spec 𝒪_{Y,y}`.

What is *not* here is the comparison `(f_* 𝒪_X)_y ≅ Γ(X', 𝒪_{X'})` itself — that is degree-zero
flat base change along `Spec 𝒪_{Y,y} ⟶ Y` and belongs elsewhere. Everything below is
unconditional and needs no hypothesis on `f` at all.

## Main results

* `Stacks.FormalFunctions.top_le_preimage_stalkBaseChangeι` — `X'` lies over every open
  neighbourhood of `y`, so a function on `f ⁻¹ U` has a canonical pullback to `X'`.
* `Stacks.FormalFunctions.pullbackToStalkBaseChange` — that pullback, and
  `Stacks.FormalFunctions.stalkBaseChangeRestrictHom` — the ring map
  `(f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})` they assemble into, whose invertibility is degree-zero flat
  base change and is **not** proved here.
* `Stacks.FormalFunctions.infinitesimalStalkRestrictHom_eq` — the canonical restriction map out
  of the stalk is that ring map followed by restriction along `X_n ⟶ X'`.
* `Stacks.FormalFunctions.stalkBaseChangeRestrictHom_toPushforwardStalk` — and it is
  `𝒪_{Y,y}`-linear, carrying the stalk of the comorphism of `f` to the structure map of `X'`.
* `Stacks.FormalFunctions.infinitesimalRestrict_eq` — **the factorization**: restricting a
  function on `f ⁻¹ U` to `X_n` is pulling it back to `X'` and then restricting along
  `X_n ⟶ X'`.
* `Stacks.FormalFunctions.isIso_appTop_infinitesimalNeighbourhoodIsoSubscheme` — the
  identification of `X_n` with the ideal-power subscheme is an isomorphism on global functions.
* `Stacks.FormalFunctions.subschemeι_appTop_eq` — on global functions it carries restriction
  along the subscheme inclusion to restriction along `X_n ⟶ X'`.
* `Stacks.FormalFunctions.appTop_infinitesimalTransition_eq` — and it carries the transition
  maps of the infinitesimal tower to those of the ideal-power tower.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
  Topology

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-! ### Pulling a function back to the base change -/

/-- **The base change `X' = X ×_Y Spec 𝒪_{Y,y}` lies over every open neighbourhood of `y`**,
because its structure morphism factors through `Spec 𝒪_{Y,y} ⟶ Y`, whose image consists of
points whose every open neighbourhood contains `y`. This is the reason a function defined only
near `y` has a pullback to the whole of `X'`. -/
public theorem top_le_preimage_stalkBaseChangeι (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    (⊤ : (stalkBaseChange f y).Opens) ≤ stalkBaseChangeι f y ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro x _
  change f.base ((stalkBaseChangeι f y).base x) ∈ U
  have hx : f.base ((stalkBaseChangeι f y).base x) =
      (Y.fromSpecStalk y).base ((stalkBaseChangeStructure f y).base x) :=
    congrArg (fun k : stalkBaseChange f y ⟶ Y => k.base x)
      (pullback.condition (f := f) (g := Y.fromSpecStalk y))
  rw [hx]
  exact le_preimage_fromSpecStalk_of_mem y U hy (x := (stalkBaseChangeStructure f y).base x)
    trivial

/-- **The pullback to `X'` of a function on `f ⁻¹ U`**, for `U` an open neighbourhood of `y`. -/
public def pullbackToStalkBaseChange (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) : Γ(stalkBaseChange f y, ⊤) :=
  ((stalkBaseChangeι f y).appLE (f ⁻¹ᵁ U) ⊤ (top_le_preimage_stalkBaseChangeι f y U hy)).hom s

/-- Global functions pulled back along `g` after a restriction `f.appLE U ⊤` is the `appLE` of
the composite `g ≫ f`. -/
private theorem appTop_appLE_apply {Z W V : Scheme.{u}} (g : Z ⟶ W) (f : W ⟶ V) (U : V.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (s : Γ(V, U)) :
    g.appTop.hom ((f.appLE U ⊤ h).hom s) =
      ((g ≫ f).appLE U ⊤ fun x _ => h (Set.mem_univ (g.base x))).hom s := by
  rw [← CommRingCat.comp_apply, ← appLE_top_eq_appTop g (top_le_preimage_top g),
    Scheme.Hom.appLE_comp_appLE]

/-- **The restriction of a function to `X_n` factors through `X'`.** This is the compatibility
that lets the tower `n ↦ Γ(X_n, 𝒪)` be computed on the affine base `Spec 𝒪_{Y,y}`. -/
public theorem infinitesimalRestrict_eq (f : X ⟶ Y) (y : Y) (n : ℕ) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    infinitesimalRestrict f y n U hy s =
      (infinitesimalιBaseChange f y n).appTop.hom (pullbackToStalkBaseChange f y U hy s) := by
  rw [pullbackToStalkBaseChange, appTop_appLE_apply]
  exact congrArg (fun φ : Γ(X, f ⁻¹ᵁ U) ⟶ Γ(infinitesimalNeighbourhood f y n, ⊤) => φ.hom s)
    (appLE_congr_hom (infinitesimalιBaseChange_comp_ι f y n) (f ⁻¹ᵁ U) ⊤ _ _).symm

/-- Restricting a function from `f ⁻¹ U` to `f ⁻¹ V` and then pulling it back to `X'` is pulling
it back directly: `X'` lies over both. -/
public theorem pullbackToStalkBaseChange_res (f : X ⟶ Y) (y : Y) {U V : Y.Opens} (hVU : V ≤ U)
    (hyV : y ∈ V) (s : Γ(X, f ⁻¹ᵁ U)) :
    pullbackToStalkBaseChange f y V hyV
        ((X.presheaf.map ((Opens.map f.base).map (homOfLE hVU)).op).hom s) =
      pullbackToStalkBaseChange f y U (hVU hyV) s := by
  change ((stalkBaseChangeι f y).appLE (f ⁻¹ᵁ V) ⊤
      (top_le_preimage_stalkBaseChangeι f y V hyV)).hom
    ((X.presheaf.map ((Opens.map f.base).map (homOfLE hVU)).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

/-- The pullbacks to `X'` of the functions on the `f ⁻¹ U`, for `U` an open neighbourhood of
`y`, as a cocone on the diagram whose colimit is the stalk `(f_* 𝒪_X)_y`. -/
public def stalkBaseChangeRestrictCocone (f : X ⟶ Y) (y : Y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ pushforwardStructurePresheaf f) where
  pt := Γ(stalkBaseChange f y, ⊤)
  ι :=
    { app U := (stalkBaseChangeι f y).appLE (f ⁻¹ᵁ U.unop.1) ⊤
        (top_le_preimage_stalkBaseChangeι f y U.unop.1 U.unop.2)
      naturality := fun U V i => by
        refine (Category.comp_id _).symm.trans ?_ |>.symm
        exact CommRingCat.hom_ext (RingHom.ext fun s =>
          (pullbackToStalkBaseChange_res f y (U := U.unop.1) (V := V.unop.1) i.unop.le
            V.unop.2 s).symm) }

/-- **The canonical ring map `(f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})`**: the germ at `y` of a function on
`f ⁻¹ U` goes to its pullback to the base change. It exists for every `f`, with no hypothesis,
because `X'` lies over every open neighbourhood of `y`.

[Stacks, Tag 02KH] part (1) at `i = 0` — degree-zero flat base change along the flat morphism
`Spec 𝒪_{Y,y} ⟶ Y` — is the assertion that this map is an isomorphism for `f` quasi-compact and
quasi-separated. That is **not** proved here. -/
public def stalkBaseChangeRestrictHom (f : X ⟶ Y) (y : Y) :
    (pushforwardStructurePresheaf f).stalk y ⟶ Γ(stalkBaseChange f y, ⊤) :=
  colimit.desc _ (stalkBaseChangeRestrictCocone f y)

/-- **The canonical map `(f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})` on germs**: the germ at `y` of a function
`s` on `f ⁻¹ U` goes to the pullback of `s` to the base change `X'`. -/
@[simp]
public theorem stalkBaseChangeRestrictHom_germ (f : X ⟶ Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    (stalkBaseChangeRestrictHom f y).hom (pushforwardStalkGerm f y U hy s) =
      pullbackToStalkBaseChange f y U hy s :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (stalkBaseChangeRestrictCocone f y) (op ⟨U, hy⟩)) s

/-- **The canonical restriction map out of the stalk factors through the base change**, as a map
and not only on germs: `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪)` is `(f_* 𝒪_X)_y ⟶ Γ(X', 𝒪_{X'})` followed by
restriction along the closed immersion `X_n ⟶ X'`. -/
public theorem infinitesimalStalkRestrictHom_eq (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalStalkRestrictHom f y n =
      stalkBaseChangeRestrictHom f y ≫ (infinitesimalιBaseChange f y n).appTop := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hyU => CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  change (infinitesimalStalkRestrictHom f y n).hom (pushforwardStalkGerm f y U hyU s) =
    (stalkBaseChangeRestrictHom f y ≫ (infinitesimalιBaseChange f y n).appTop).hom
      (pushforwardStalkGerm f y U hyU s)
  rw [infinitesimalStalkRestrictHom_germ, CommRingCat.comp_apply,
    stalkBaseChangeRestrictHom_germ, infinitesimalRestrict_eq]

/-- **The canonical map out of the stalk is `𝒪_{Y,y}`-linear**: it carries the stalk of the
comorphism of `f` to the structure map of `X'` over `Spec 𝒪_{Y,y}`, read at `⊤`. Without this,
the comparison with [Stacks, Tag 02OB] — which is a statement about modules over the base ring
— could not even be formulated. -/
public theorem stalkBaseChangeRestrictHom_toPushforwardStalk (f : X ⟶ Y) (y : Y) :
    toPushforwardStalk f y ≫ stalkBaseChangeRestrictHom f y =
      (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv ≫ (stalkBaseChangeStructure f y).appTop := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hyU => CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  have hgerm : (toPushforwardStalk f y).hom ((Y.presheaf.germ U y hyU).hom t) =
      pushforwardStalkGerm f y U hyU ((f.app U).hom t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (F := Y.presheaf)
      (G := pushforwardStructurePresheaf f) U y hyU f.c t
  change (stalkBaseChangeRestrictHom f y).hom
      ((toPushforwardStalk f y).hom ((Y.presheaf.germ U y hyU).hom t)) =
    (stalkBaseChangeStructure f y).appTop.hom
      ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom ((Y.presheaf.germ U y hyU).hom t))
  rw [hgerm, stalkBaseChangeRestrictHom_germ, pullbackToStalkBaseChange,
    ← fromSpecStalk_appLE_top_apply, appTop_appLE_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ : Γ(Y, U) ⟶ Γ(stalkBaseChange f y, ⊤) => φ.hom t)
    (appLE_congr_hom (pullback.condition (f := f) (g := Y.fromSpecStalk y)) U ⊤ _ _)

/-! ### The identification on global functions -/

/-- The global functions on `X_n` are the global functions on the closed subscheme of `X'` cut
out by `(𝔪_y 𝒪_{X'}) ^ n`. -/
public instance isIso_appTop_infinitesimalNeighbourhoodIsoSubscheme (f : X ⟶ Y) (y : Y) (n : ℕ) :
    IsIso (infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop := by
  refine ⟨(infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  · rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    rfl

/-- On global functions, restriction along the inclusion of the subscheme of
`(𝔪_y 𝒪_{X'}) ^ n` is restriction along `X_n ⟶ X'` followed by the identification. -/
public theorem subschemeι_appTop_eq (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (infinitesimalBaseIdealSheaf f y ^ n).subschemeι.appTop =
      (infinitesimalιBaseChange f y n).appTop ≫
        (infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop := by
  rw [← Scheme.Hom.comp_appTop, infinitesimalNeighbourhoodIsoSubscheme_hom_comp_ιBaseChange]

/-- On global functions, the transition maps of the infinitesimal tower correspond to those of
the tower of ideal-power subschemes. -/
public theorem appTop_infinitesimalTransition_eq (f : X ⟶ Y) (y : Y) {n m : ℕ} (h : n ≤ m) :
    (infinitesimalTransition f y h).appTop ≫
        (infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop =
      (infinitesimalNeighbourhoodIsoSubscheme f y m).hom.appTop ≫
        (Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.pow_le_pow_of_le (infinitesimalBaseIdealSheaf f y) h)).appTop := by
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    infinitesimalNeighbourhoodIsoSubscheme_hom_comp_transition]

end Stacks.FormalFunctions

end
