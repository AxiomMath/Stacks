module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompFunctoriality.Basic

/-!
# Pulled-back sections read over an open that is only propositionally the inverse image

Every lemma in this file is stated with the scheme, the morphism, the module, the opens and the
section all **variables**, and every identification of two opens is a hypothesis between two
variables, so that each proof is a `subst` followed by the corresponding statement of
`Stacks.AlgebraicGeometry.PullbackUnit` at the reflexive case.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.pullbackSectionAt`

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

universe u

variable {X Y Z : Scheme.{u}}

/-- **A pulled-back section, read over an open that is only propositionally the inverse
image.** -/
public def pullbackSectionAt (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ T = V) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullback f).obj M).val.obj (op V) :=
  ((Scheme.Modules.pullback f).obj M).val.map (eqToHom (congrArg op h))
    (pullbackSectionOn f M T s)

/-- At the inverse image itself there is nothing to transport. -/
public theorem pullbackSectionAt_rfl (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens)
    (h : f ⁻¹ᵁ T = f ⁻¹ᵁ T) (s : M.val.obj (op T)) :
    pullbackSectionAt f M T (f ⁻¹ᵁ T) h s = pullbackSectionOn f M T s := by
  simp [pullbackSectionAt]

/-- The same at the composite spelling of the inverse image: `(f ≫ g) ⁻¹ᵁ T` and
`f ⁻¹ᵁ (g ⁻¹ᵁ T)` are definitionally equal, and at the level of variables that identification is
free. -/
public theorem pullbackSectionAt_comp_rfl (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (T : Z.Opens)
    (h : (f ≫ g) ⁻¹ᵁ T = f ⁻¹ᵁ g ⁻¹ᵁ T) (s : M.val.obj (op T)) :
    pullbackSectionAt (f ≫ g) M T (f ⁻¹ᵁ g ⁻¹ᵁ T) h s = pullbackSectionOn (f ≫ g) M T s :=
  pullbackSectionAt_rfl (f ≫ g) M T h s

/-- **A morphism of modules commutes with the transport along an equality of opens.** -/
public theorem val_app_map_eqToHom {W : Scheme.{u}} {P Q : W.Modules} (α : P ⟶ Q)
    {V V' : W.Opens} (h : V = V') (x : P.val.obj (op V)) :
    α.val.app (op V') (P.val.map (eqToHom (congrArg op h)) x)
      = Q.val.map (eqToHom (congrArg op h)) (α.val.app (op V) x) :=
  PresheafOfModules.naturality_apply α.val (eqToHom (congrArg op h)) x

/-- The transport along a reflexive equality of opens is the identity on sections. -/
public theorem map_eqToHom_rfl {W : Scheme.{u}} (M : W.Modules) (T : W.Opens) (h : T = T)
    (s : M.val.obj (op T)) : M.val.map (eqToHom (congrArg op h)) s = s := by
  simp
  rfl

/-- **Two transported pulled-back sections agree as soon as the opens and the sections do.** -/
public theorem pullbackSectionAt_congr (f : X ⟶ Y) (M : Y.Modules) {T T' : Y.Opens}
    (hT : T = T') {V : X.Opens} (h : f ⁻¹ᵁ T = V) (h' : f ⁻¹ᵁ T' = V)
    (s : M.val.obj (op T)) (s' : M.val.obj (op T'))
    (hs : M.val.map (eqToHom (congrArg op hT)) s = s') :
    pullbackSectionAt f M T V h s = pullbackSectionAt f M T' V h' s' := by
  subst hT
  rw [← hs]
  simp only [pullbackSectionAt]
  exact congrArg (fun z => ((Scheme.Modules.pullback f).obj M).val.map
      (eqToHom (congrArg op h)) z)
    (congrArg (pullbackSectionOn f M T) (map_eqToHom_rfl M T rfl s).symm)

/-- **The functor image of a morphism, on a transported pulled-back section.** -/
public theorem pullback_map_pullbackSectionAt (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (T : Y.Opens) {V : X.Opens} (h : f ⁻¹ᵁ T = V) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op V) (pullbackSectionAt f M T V h s)
      = pullbackSectionAt f N T V h (φ.val.app (op T) s) := by
  subst h
  rw [pullbackSectionAt_rfl, pullbackSectionAt_rfl]
  exact pullback_map_pullbackSectionOn f φ T s

/-- **The pseudofunctoriality isomorphism for a composite, backwards, on a transported
pulled-back section.** -/
public theorem pullbackComp_inv_pullbackSectionAt (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (T : Z.Opens) {V₁ : Y.Opens} (h₁ : g ⁻¹ᵁ T = V₁) {V : X.Opens} (h : f ⁻¹ᵁ V₁ = V)
    (h₂ : (f ≫ g) ⁻¹ᵁ T = V) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op V)
        (pullbackSectionAt (f ≫ g) M T V h₂ s)
      = pullbackSectionAt f ((Scheme.Modules.pullback g).obj M) V₁ V h
          (pullbackSectionAt g M T V₁ h₁ s) := by
  subst h₁
  subst h
  rw [pullbackSectionAt_comp_rfl, pullbackSectionAt_rfl, pullbackSectionAt_rfl]
  exact pullbackComp_inv_pullbackSectionOn f g M T s

/-- **The pseudofunctoriality isomorphism for a composite, forwards, on a transported
pulled-back section.** -/
public theorem pullbackComp_hom_pullbackSectionAt (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (T : Z.Opens) {V₁ : Y.Opens} (h₁ : g ⁻¹ᵁ T = V₁) {V : X.Opens} (h : f ⁻¹ᵁ V₁ = V)
    (h₂ : (f ≫ g) ⁻¹ᵁ T = V) (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op V)
        (pullbackSectionAt f ((Scheme.Modules.pullback g).obj M) V₁ V h
          (pullbackSectionAt g M T V₁ h₁ s))
      = pullbackSectionAt (f ≫ g) M T V h₂ s := by
  subst h₁
  subst h
  rw [pullbackSectionAt_comp_rfl, pullbackSectionAt_rfl, pullbackSectionAt_rfl]
  exact pullbackComp_hom_pullbackSectionOn f g M T s

/-- **The congruence isomorphism of two equal morphisms, forwards, on a transported pulled-back
section.** -/
public theorem pullbackCongr_hom_pullbackSectionAt {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (T : Y.Opens) {V : X.Opens} (h : f ⁻¹ᵁ T = V) (h' : g ⁻¹ᵁ T = V)
    (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op V)
        (pullbackSectionAt f M T V h s)
      = pullbackSectionAt g M T V h' s := by
  subst hf
  exact pullbackCongr_refl_hom_app f _ M V _

/-- **The congruence isomorphism of two equal morphisms, backwards, on a transported pulled-back
section.** -/
public theorem pullbackCongr_inv_pullbackSectionAt {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (T : Y.Opens) {V : X.Opens} (h : g ⁻¹ᵁ T = V) (h' : f ⁻¹ᵁ T = V)
    (s : M.val.obj (op T)) :
    ((Scheme.Modules.pullbackCongr hf).inv.app M).val.app (op V)
        (pullbackSectionAt g M T V h s)
      = pullbackSectionAt f M T V h' s := by
  subst hf
  exact pullbackCongr_refl_inv_app f _ M V _

/-- **A pulled-back section along an open immersion, written through the identification of
restriction with the inverse image.** The inner factor is the unit of the restriction adjunction,
which on sections is an ordinary restriction map. -/
public theorem pullbackSectionOn_eq_restrictIso (g : X ⟶ Y) [IsOpenImmersion g] (M : Y.Modules)
    (T : Y.Opens) (t : M.val.obj (op T)) :
    pullbackSectionOn g M T t =
      ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val.app (op (g ⁻¹ᵁ T))
        (((Scheme.Modules.restrictAdjunction g).unit.app M).val.app (op T) t) :=
  (congrArg (fun ρ : M ⟶ (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pullback g).obj M) => ρ.val.app (op T) t)
    (Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback
      g M)).symm

/-- The same for a transported pulled-back section. -/
public theorem pullbackSectionAt_eq_restrictIso (g : X ⟶ Y) [IsOpenImmersion g] (M : Y.Modules)
    (T : Y.Opens) {V : X.Opens} (h : g ⁻¹ᵁ T = V) (t : M.val.obj (op T)) :
    pullbackSectionAt g M T V h t =
      ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val.app (op V)
        (((Scheme.Modules.restrictFunctor g).obj M).val.map (eqToHom (congrArg op h))
          (((Scheme.Modules.restrictAdjunction g).unit.app M).val.app (op T) t)) := by
  refine Eq.trans ?_ (val_app_map_eqToHom
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) h _).symm
  exact congrArg (fun z => ((Scheme.Modules.pullback g).obj M).val.map
    (eqToHom (congrArg op h)) z) (pullbackSectionOn_eq_restrictIso g M T t)

/-- **Two restriction maps of a module sheaf between two opens compose to the identity.** The
opens of a scheme form a poset, so the composite is the identity morphism, whatever the two
morphisms are. -/
public theorem map_comp_self {W : Scheme.{u}} (M : W.Modules) {U V : W.Opens}
    (i : op U ⟶ op V) (j : op V ⟶ op U) (x : M.val.obj (op U)) :
    M.val.map j (M.val.map i x) = x := by
  have h : i ≫ j = 𝟙 _ := Subsingleton.elim _ _
  have hmap : M.presheaf.map i ≫ M.presheaf.map j = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
  exact CategoryTheory.congr_fun hmap x

/-- **The unit of the restriction adjunction at the image of an open is the identity on
sections**, read through the identification of the inverse image of that image with the open.

The unit is the restriction map from `U` to `g ''ᵁ (g ⁻¹ᵁ U)`, so at `U = g ''ᵁ Z` it is a
restriction map between two equal opens, and the transport back is a second one; the composite is
the identity by `map_comp_self`. -/
public theorem restrictUnit_preimage_image (g : X ⟶ Y) [IsOpenImmersion g] (M : Y.Modules)
    (Z₀ : X.Opens) (hpi : g ⁻¹ᵁ (g ''ᵁ Z₀) = Z₀) (t : M.val.obj (op (g ''ᵁ Z₀))) :
    ((Scheme.Modules.restrictFunctor g).obj M).val.map (eqToHom (congrArg op hpi))
        (((Scheme.Modules.restrictAdjunction g).unit.app M).val.app (op (g ''ᵁ Z₀)) t) = t :=
  map_comp_self M (homOfLE (g.image_preimage_le (g ''ᵁ Z₀))).op
    (eqToHom (congrArg op (congrArg (fun W => g ''ᵁ W) hpi))) t

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
