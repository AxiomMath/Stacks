module

public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Basic
public import StacksFrontier.Algebra.Module.Reflexive.RingEquiv

/-!
# Stalks of a restriction along an open immersion, and reflexivity of a stalk

Let `j : W ⟶ X` be an open immersion of schemes and let `F` be an `𝒪_X`-module.  At a point `w`
of `W` the stalk of `F|_W` is the stalk of `F` at `j w`, and this identification is *semilinear*
over the isomorphism `𝒪_{X, j w} ≅ 𝒪_{W, w}` of local rings: it is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` on underlying abelian groups, and the
scalar compatibility is a germ computation.

Consequently the stalk of `F|_W` at `w` is a reflexive `𝒪_{W, w}`-module exactly when the stalk
of `F` at `j w` is a reflexive `𝒪_{X, j w}`-module.  That is the step by which a reflexivity
hypothesis on an open subscheme becomes one on the ambient scheme, and it is what
[Stacks, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) needs in order to replace a
coherent extension by its reflexive hull.

## Main definitions

* `restrictStalkHom`: the comparison map `(F|_W)_w ⟶ F_{j w}` on stalks, at the `modStalk`
  spelling used by `StacksFrontier/AlgebraicGeometry/ReflexiveStalk/Basic.lean`.
* `restrictStalkRingEquiv`: the induced equivalence `𝒪_{W, w} ≃+* 𝒪_{X, j w}` of local rings.
* `restrictStalkAddEquiv`: `restrictStalkHom` as an additive equivalence.
* `stalkLinearEquivOfIso`: an isomorphism of `𝒪_X`-modules induces a linear equivalence of
  stalks.

## Main results

* `restrictStalkHom_smul`: **the scalar compatibility**, `restrictStalkHom (r • m) =
  restrictStalkRingEquiv r • restrictStalkHom m`.
* `module_isReflexive_modStalk_of_restrict`: reflexivity of the stalk of `F|_W` at `w` gives
  reflexivity of the stalk of `F` at `j w`.
* `module_isReflexive_modStalk_of_iso`: reflexivity of a stalk is invariant under isomorphism of
  modules.

## Implementation notes

The scalar compatibility is proved once, in `restrictStalkHom'_stalkMap_smul`, at the
`F.presheaf.stalk` spelling of a stalk, where the scalar `a` of the ambient local ring can be
pushed forward by `j.stalkMap w` and the germ formulas
`AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app`,
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` and
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` apply directly.  It is then
restated once, as `restrictStalkHom_smul`, at the `modStalk`/`ringStalk` spelling that the
reflexivity statements of `ReflexiveStalk/Basic.lean` use.  The restatement is necessary and not
cosmetic: the two spellings of the local ring are equal only definitionally, so the two module
structures on a stalk, while equal by `rfl`, are found by instance search for one spelling of
the scalars each, and `•` resolves syntactically.  No transparency option is needed — the
restatement discharges by a bare `exact`.

Everything here is stated for an arbitrary open immersion rather than for the inclusion of an
open subscheme, which is the generality the germ computation naturally has.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X W : Scheme.{u}}

/-! ### Stalks and isomorphisms -/

/-- An isomorphism of `𝒪_X`-modules induces a linear equivalence of stalks at every point. -/
public noncomputable def stalkLinearEquivOfIso {A B : X.Modules} (e : A ≅ B) (x : X) :
    modStalk A x ≃ₗ[ringStalk X.sheaf x] modStalk B x :=
  LinearEquiv.ofLinearMap (stalkHom e.hom x) (stalkHom e.inv x)
    (by rw [← stalkHom_comp, e.inv_hom_id, stalkHom_id])
    (by rw [← stalkHom_comp, e.hom_inv_id, stalkHom_id])

@[simp] public theorem stalkLinearEquivOfIso_apply {A B : X.Modules} (e : A ≅ B) (x : X)
    (m : modStalk A x) : stalkLinearEquivOfIso e x m = stalkHom e.hom x m := rfl

/-- Reflexivity of a stalk is invariant under isomorphism of the modules. -/
public theorem module_isReflexive_modStalk_of_iso {A B : X.Modules} (e : A ≅ B) (x : X)
    (h : Module.IsReflexive (ringStalk X.sheaf x) (modStalk A x)) :
    Module.IsReflexive (ringStalk X.sheaf x) (modStalk B x) :=
  let := h
  Module.equiv (stalkLinearEquivOfIso e x)

/-! ### The comparison of stalks along an open immersion -/

/-- The comparison map from the stalk of a restriction `F|_W` at `w` to the stalk of `F` at
`j w`.  It is `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, read at the `modStalk`
spelling of a stalk. -/
public noncomputable def restrictStalkHom (j : W ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (w : W) : modStalk (F.restrict j) w ⟶ modStalk F (j w) :=
  (Scheme.Modules.restrictStalkNatIso j w).hom.app F

public instance isIso_restrictStalkHom (j : W ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (w : W) : IsIso (restrictStalkHom j F w) :=
  ((Scheme.Modules.restrictStalkNatIso j w).app F).isIso_hom

/-- The equivalence of local rings induced by an open immersion: the stalk map of `j` at `w` is
an isomorphism, and this is its inverse read as an equivalence of rings. -/
public noncomputable def restrictStalkRingEquiv (j : W ⟶ X) [IsOpenImmersion j] (w : W) :
    ringStalk W.sheaf w ≃+* ringStalk X.sheaf (j w) :=
  (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.symm

/-- The comparison map on stalks, at the spelling in which the scalar of the ambient local ring
is pushed forward along the stalk map of `j`.  This is where the germ computation happens; the
form consumed elsewhere is `restrictStalkHom_smul`. -/
private noncomputable def restrictStalkHom' (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) :
    (F.restrict j).presheaf.stalk w ⟶ F.presheaf.stalk (j w) :=
  (Scheme.Modules.restrictStalkNatIso j w).hom.app F

/-- **The germ computation.**  The comparison map on stalks is semilinear over the stalk map of
`j`: a scalar `a` of `𝒪_{X, j w}` acting through `j.stalkMap w` on the stalk of `F|_W` becomes
`a` acting on the stalk of `F`.

Both sides are computed on germs over a common open neighbourhood `T'` of `w`, where the
restriction identification `F.restrictAppIso j T'` carries the action of `𝒪_W(T')` to the action
of `𝒪_X(j ''ᵁ T')` by `Scheme.Modules.smul_restrictAppIso_hom_apply`. -/
private theorem restrictStalkHom'_stalkMap_smul (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) (a : X.presheaf.stalk (j w))
    (m : (F.restrict j).presheaf.stalk w) :
    restrictStalkHom' j F w ((j.stalkMap w).hom a • m) = a • restrictStalkHom' j F w m := by
  let G := F.restrict j
  obtain ⟨V, hV, r, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨T, hT, t, rfl⟩ := G.presheaf.exists_germ_eq m
  let T' : W.Opens := T ⊓ j ⁻¹ᵁ V
  have hT' : w ∈ T' := ⟨hT, hV⟩
  let r' : Γ(W, T') := W.presheaf.map (homOfLE inf_le_right).op (j.app V r)
  let t' : Γ(G, T') := G.presheaf.map (homOfLE inf_le_left).op t
  let J : X.Opens := j ''ᵁ T'
  have hJ : j w ∈ J := ⟨w, hT', rfl⟩
  have hJV : J ≤ V := by
    rintro x ⟨z, hz, rfl⟩
    exact hz.2
  let rJ : Γ(X, J) := X.presheaf.map (homOfLE hJV).op r
  have hr : (j.stalkMap w).hom (X.presheaf.germ V (j w) hV r) =
      W.presheaf.germ T' w hT' r' := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (W.presheaf.germ_res_apply (homOfLE inf_le_right) w hT' (j.app V r)).symm
  have hm : G.presheaf.germ T w hT t = G.presheaf.germ T' w hT' t' :=
    (G.presheaf.germ_res_apply (homOfLE inf_le_left) w hT' t).symm
  have hrJ : X.presheaf.germ V (j w) hV r = X.presheaf.germ J (j w) hJ rJ :=
    (X.presheaf.germ_res_apply (homOfLE hJV) (j w) hJ r).symm
  have hscalar : (j.appIso T').inv r' = rJ :=
    congrArg (fun z : Γ(X, V) ⟶ Γ(X, J) => z r)
      (Scheme.Hom.appLE_appIso_inv j (inf_le_right : T' ≤ j ⁻¹ᵁ V))
  let eT : Γ(G, T') ≅ Γ(F, J) := F.restrictAppIso j T'
  let tF : Γ(F, J) := eT.hom t'
  have hsection : eT.hom (r' • t') = rJ • tF := by
    rw [← hscalar]
    exact Scheme.Modules.smul_restrictAppIso_hom_apply j F T' r' t'
  rw [hr, hm, hrJ]
  calc
    _ = restrictStalkHom' j F w (G.presheaf.germ T' w hT' (r' • t')) :=
      congrArg (restrictStalkHom' j F w) (PresheafOfModules.germ_smul G.val w T' hT' r' t').symm
    _ = F.presheaf.germ J (j w) hJ (eT.hom (r' • t')) :=
      congrArg (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z (r' • t'))
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT')
    _ = F.presheaf.germ J (j w) hJ (rJ • tF) := by rw [hsection]
    _ = X.presheaf.germ J (j w) hJ rJ • F.presheaf.germ J (j w) hJ tF :=
      PresheafOfModules.germ_smul F.val (j w) J hJ rJ tF
    _ = _ := congrArg (X.presheaf.germ J (j w) hJ rJ • ·)
      (congrArg (fun z : Γ(G, T') ⟶ F.presheaf.stalk (j w) => z t')
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j w F hT')).symm

/-- **The comparison of stalks along an open immersion is semilinear** over the equivalence
`restrictStalkRingEquiv` of local rings. -/
public theorem restrictStalkHom_smul (j : W ⟶ X) [IsOpenImmersion j] (F : X.Modules) (w : W)
    (r : ringStalk W.sheaf w) (m : modStalk (F.restrict j) w) :
    restrictStalkHom j F w (r • m)
      = restrictStalkRingEquiv j w r • restrictStalkHom j F w m := by
  have hr : (j.stalkMap w).hom (restrictStalkRingEquiv j w r) = r :=
    (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.apply_symm_apply r
  have h := restrictStalkHom'_stalkMap_smul j F w (restrictStalkRingEquiv j w r) m
  rw [hr] at h
  exact h

/-- The comparison of stalks along an open immersion, as an additive equivalence. -/
public noncomputable def restrictStalkAddEquiv (j : W ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    (w : W) : modStalk (F.restrict j) w ≃+ modStalk F (j w) :=
  AddEquiv.ofBijective (restrictStalkHom j F w).hom
    (ConcreteCategory.bijective_of_isIso (restrictStalkHom j F w))

@[simp] public theorem restrictStalkAddEquiv_apply (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W) (m : modStalk (F.restrict j) w) :
    restrictStalkAddEquiv j F w m = restrictStalkHom j F w m := rfl

/-- **Reflexivity of a stalk crosses an open immersion.**  If the stalk of `F|_W` at `w` is a
reflexive `𝒪_{W, w}`-module then the stalk of `F` at `j w` is a reflexive `𝒪_{X, j w}`-module.

This is `Module.IsReflexive.of_ringEquiv` applied to `restrictStalkRingEquiv` and
`restrictStalkAddEquiv`, whose compatibility is `restrictStalkHom_smul`. -/
public theorem module_isReflexive_modStalk_of_restrict (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (w : W)
    (h : Module.IsReflexive (ringStalk W.sheaf w) (modStalk (F.restrict j) w)) :
    Module.IsReflexive (ringStalk X.sheaf (j w)) (modStalk F (j w)) :=
  let := h
  Module.IsReflexive.of_ringEquiv (restrictStalkRingEquiv j w)
    (restrictStalkAddEquiv j F w) (restrictStalkHom_smul j F w)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
