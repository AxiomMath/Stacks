module

public import StacksFrontier.AlgebraicGeometry.ModuleStalkTensor.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.PullbackStalkTensor

/-!
# The stalk of a pullback of sheaves of modules on a scheme, with a concrete left adjoint

`Stacks.ModuleStalkTensor.stalkPullbackModulesIso` computes the stalk of
`AlgebraicGeometry.Scheme.Modules.pullback g` at a point of the source, `(g^*M)_t ≅ L (M_{g t})`,
for a functor `L` given together with an adjunction exhibiting it as left adjoint to restriction
of scalars along the stalk map **taken in `RingCat`**. For a morphism of schemes `g : T ⟶ S` and
`t : T`, `Stacks.PullbackTensorIso.stalkExtendScalarsAdj g.toLRSHom.toShHom t` is such an
adjunction, the scheme-level stalk ring map
`Stacks.ModuleSkyscraper.stalkRingMap … g.toRingCatSheafHom t` and the ringed-space-level
`ringedSpaceStalkRingMap` of the underlying morphism being the same map. So the stalk of a
pullback on a scheme is `𝒪_{T,t} ⊗_{𝒪_{S,g t}} M_{g t}`.

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackStalkScheme.stalkExtendScalars`: extension of scalars along
  the stalk map of a morphism of schemes.
* `Stacks.AlgebraicGeometry.PullbackStalkScheme.stalkAdj`: the adjunction, at the stalk map of a
  morphism of schemes.
* `Stacks.AlgebraicGeometry.PullbackStalkScheme.stalkPullbackIso`: **the stalk of a pullback of
  sheaves of modules on a scheme**, with the left adjoint concrete.

## Main results

* `Stacks.AlgebraicGeometry.PullbackStalkScheme.isZero_stalk_pullback`: the stalk of a pullback
  vanishes wherever the stalk of the source vanishes.
* `Stacks.AlgebraicGeometry.PullbackStalkScheme.nontrivial_stalk_pullback_of_iso_free`: the
  stalk of a pullback is nontrivial wherever the stalk of the source is free of rank one, given
  that the structure-sheaf stalk at the chosen point of the source scheme is nontrivial.

* `Stacks.AlgebraicGeometry.PullbackStalkScheme.not_isIso_of_stalk_free_of_stalk_isZero`: **a
  comparison map between two pullbacks is not an isomorphism when one stalk separates them** —
  the stalk of the source's target free of rank one, the stalk of the other target zero.

## Transparency notes

* `ModuleCat.of _ (Stacks.ModuleSkyscraper.Stalk T.ringCatSheaf t)` does **not** elaborate at the
  base ring the adjunction fixes: the ring is inferred in the spelling
  `Stacks.PullbackTensorIso.ringCatStalk T.toSheafedSpace t`, the two are one unfolding apart,
  and `Module R R` is then not found. `nontrivial_obj_of_iso_free` therefore takes nontriviality
  of the *base ring* and forms the free module itself, where the ring is a plain type.
* `ModuleCat.isZero_of_subsingleton` is applied to the composed-functor spelling
  `(pullback g ⋙ stalkFunctor t).obj G` explicitly: instance search does not see through
  `CategoryTheory.Functor.comp` to the `Subsingleton` hypothesis stated on
  `(stalkFunctor t).obj ((pullback g).obj G)`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.PullbackStalkScheme

universe u

section ModuleCatAdjunction

variable {R Sr : Type u} [Ring R] [Ring Sr]
  {L : ModuleCat.{u} R ⥤ ModuleCat.{u} Sr} {G : ModuleCat.{u} Sr ⥤ ModuleCat.{u} R}

/-! The lemmas below are stated for a left adjoint `L` between categories of modules, with `G`
its right adjoint; only `nontrivial_obj_of_iso_free` needs `G` to be restriction of scalars. -/

/-- A left adjoint between categories of modules carries a zero module to a zero module. -/
public theorem isZero_obj_of_isZero (adj : L ⊣ G) (M : ModuleCat.{u} R) (hM : IsZero M) :
    IsZero (L.obj M) := by
  rw [IsZero.iff_id_eq_zero]
  exact (adj.homEquiv M (L.obj M)).injective (hM.eq_of_src _ _)

/-- If some morphism group out of `M` into the image of the right adjoint is not a subsingleton,
then the value of the left adjoint at `M` is nontrivial. -/
public theorem nontrivial_obj_of_not_subsingleton_hom (adj : L ⊣ G) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} Sr) (h : ¬ Subsingleton (M ⟶ G.obj N)) : Nontrivial (L.obj M) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hz : IsZero (L.obj M) := ModuleCat.isZero_of_subsingleton (L.obj M)
  exact h ⟨fun f₁ f₂ => by
    refine (adj.homEquiv M N).symm.injective ?_
    exact hz.eq_of_src _ _⟩

/-- The morphism group from the free rank-one module into a nontrivial module is not a
subsingleton. -/
public theorem not_subsingleton_hom_free (P : ModuleCat.{u} R) [Nontrivial P] :
    ¬ Subsingleton (ModuleCat.of R R ⟶ P) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  intro hsub
  have : (ModuleCat.ofHom (LinearMap.toSpanSingleton R P x)) = (0 : ModuleCat.of R R ⟶ P) :=
    hsub.allEq _ _
  have hx' : (LinearMap.toSpanSingleton R P x) 1 = (0 : P) := by
    rw [show (LinearMap.toSpanSingleton R P x) 1
      = (ModuleCat.ofHom (LinearMap.toSpanSingleton R P x)).hom 1 from rfl, this]
    simp
  exact hx (by simpa using hx')

/-- A module isomorphic to a nontrivial module is nontrivial. -/
private theorem nontrivial_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N) (h : Nontrivial M) :
    Nontrivial N := by
  rw [← not_subsingleton_iff_nontrivial]
  exact fun hs => not_subsingleton_iff_nontrivial.mpr h
    (ModuleCat.subsingleton_of_isZero ((ModuleCat.isZero_of_subsingleton N).of_iso e))

/-- If `M` is free of rank one and the right adjoint carries `N` to a nontrivial module, the
value of the left adjoint at `M` is nontrivial. -/
public theorem nontrivial_obj_of_iso_free {φ : R →+* Sr}
    (adj : L ⊣ ModuleCat.restrictScalars φ) {M : ModuleCat.{u} R}
    (e : M ≅ ModuleCat.of R R) (hSr : Nontrivial Sr) :
    Nontrivial (L.obj M) := by
  let _ : Nontrivial
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of Sr Sr)) := hSr
  refine nontrivial_obj_of_not_subsingleton_hom adj M (ModuleCat.of Sr Sr) (fun hsub => ?_)
  refine not_subsingleton_hom_free (R := R)
    ((ModuleCat.restrictScalars φ).obj (ModuleCat.of Sr Sr)) ⟨fun f₁ f₂ => ?_⟩
  calc f₁ = e.inv ≫ e.hom ≫ f₁ := by rw [Iso.inv_hom_id_assoc]
    _ = e.inv ≫ e.hom ≫ f₂ := by rw [hsub.allEq (e.hom ≫ f₁) (e.hom ≫ f₂)]
    _ = f₂ := by rw [Iso.inv_hom_id_assoc]

end ModuleCatAdjunction

section SchemeStalk

variable {T S : Scheme.{u}} (g : T ⟶ S) (t : T)

/-- **Extension of scalars along the stalk map of a morphism of schemes**: its value on `N` is
`𝒪_{T,t} ⊗_{𝒪_{S,g t}} N`, both stalks taken in `CommRingCat`. -/
public abbrev stalkExtendScalars :=
  Stacks.PullbackTensorIso.stalkExtendScalars g.toLRSHom.toShHom t

/-- Extension of scalars along the stalk map of a morphism of schemes is left adjoint to
restriction of scalars along it. This is the ringed-space adjunction
`Stacks.PullbackTensorIso.stalkExtendScalarsAdj` of the underlying morphism of ringed spaces: the
scheme-level stalk ring map `Stacks.ModuleSkyscraper.stalkRingMap … g.toRingCatSheafHom t` and the
ringed-space-level `Stacks.ModuleSkyscraper.ringedSpaceStalkRingMap` of the underlying morphism
are the same map. -/
public def stalkAdj :
    stalkExtendScalars g t ⊣
      ModuleCat.restrictScalars.{u}
        (Stacks.ModuleSkyscraper.stalkRingMap g.base T.ringCatSheaf S.ringCatSheaf
          g.toRingCatSheafHom t).hom :=
  Stacks.PullbackTensorIso.stalkExtendScalarsAdj g.toLRSHom.toShHom t

/-- **The stalk of a pullback of sheaves of modules on a scheme**:
`(g^*M)_t ≅ 𝒪_{T,t} ⊗_{𝒪_{S,g t}} M_{g t}`, naturally in `M`. -/
public def stalkPullbackIso :
    Scheme.Modules.pullback g ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor T.ringCatSheaf t ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor S.ringCatSheaf (g.base t) ⋙
        stalkExtendScalars g t :=
  Stacks.ModuleStalkTensor.stalkPullbackModulesIso g t (stalkAdj g t)

/-- **The stalk of a pullback vanishes where the stalk of the source vanishes.** -/
public theorem isZero_stalk_pullback (G : S.Modules)
    (hG : IsZero
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor S.ringCatSheaf (g.base t)).obj G)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor T.ringCatSheaf t).obj
      ((Scheme.Modules.pullback g).obj G)) :=
  (isZero_obj_of_isZero (stalkAdj g t) _ hG).of_iso ((stalkPullbackIso g t).app G)

/-- **The stalk of a pullback is nontrivial where the stalk of the source is free of rank one**,
provided the stalk of the structure sheaf at the chosen point of the source is nontrivial — which
it is for a scheme, the stalks being local rings. -/
public theorem nontrivial_stalk_pullback_of_iso_free (G : S.Modules)
    (e : (AlgebraicGeometry.SheafOfModules.stalkFunctor S.ringCatSheaf (g.base t)).obj G ≅
      ModuleCat.of _ (Stacks.ModuleSkyscraper.Stalk S.ringCatSheaf (g.base t)))
    (hT : Nontrivial (Stacks.ModuleSkyscraper.Stalk T.ringCatSheaf t)) :
    Nontrivial ((AlgebraicGeometry.SheafOfModules.stalkFunctor T.ringCatSheaf t).obj
      ((Scheme.Modules.pullback g).obj G)) := by
  have hN := nontrivial_obj_of_iso_free (stalkAdj g t) e hT
  exact nontrivial_of_iso ((stalkPullbackIso g t).app G).symm hN

end SchemeStalk

section Separation

/-- **A comparison map between two pullbacks is not an isomorphism when it separates on one
stalk.** If at a point `x` of the common source the stalk of `G` is free of rank one and the
stalk of `H` vanishes, then no morphism `f^*G ⟶ k^*H` is an isomorphism. -/
public theorem not_isIso_of_stalk_free_of_stalk_isZero {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (k : X ⟶ Z) (x : X) (G : Y.Modules) (H : Z.Modules)
    (eG : (AlgebraicGeometry.SheafOfModules.stalkFunctor Y.ringCatSheaf (f.base x)).obj G ≅
      ModuleCat.of _ (Stacks.ModuleSkyscraper.Stalk Y.ringCatSheaf (f.base x)))
    (hX : Nontrivial (Stacks.ModuleSkyscraper.Stalk X.ringCatSheaf x))
    (hH : IsZero
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf (k.base x)).obj H))
    (φ : (Scheme.Modules.pullback f).obj G ⟶ (Scheme.Modules.pullback k).obj H) :
    ¬ IsIso φ := by
  intro hφ
  have h1 := nontrivial_stalk_pullback_of_iso_free f x G eG hX
  have h2 := isZero_stalk_pullback k x H hH
  have := nontrivial_of_iso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).mapIso
    (@asIso _ _ _ _ φ hφ)) h1
  exact (not_subsingleton_iff_nontrivial.mpr this) (ModuleCat.subsingleton_of_isZero h2)

end Separation

end Stacks.AlgebraicGeometry.PullbackStalkScheme

end
