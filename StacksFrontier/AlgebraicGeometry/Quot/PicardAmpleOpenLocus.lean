module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus

/-!
# The relatively ample locus of a Picard stack is open

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` of a big fppf site and
let `Picardstack_{X/Y}` be the Picard stack of Section 0372. The objects `(T, L)` with `L` ample on
`X_T/T` (`AlgebraicGeometry.Space.picardAmple`) have an open locus at every scheme-valued point:
for an object `(U, L)` over a scheme `U`, there is an open subscheme `V ⊆ U` such that a scheme
`T ⟶ U` factors through `V` if and only if the pullback of `(U, L)` to `T` is relatively ample.

As in the proof of Stacks 0D41, Stacks 0D3D applied to `X_U ⟶ U` and `L` gives an open subspace
of `U`, which is an open subscheme
(`AlgebraicGeometry.Space.exists_openImmersion_of_isOpenSubspace`), and the pullback of `(U, L)`
to `T` is the base change of `X_U ⟶ U` along `T ⟶ U` with the pullback of `L`. Stacks 0D3D
enters as the hypothesis `h0D3D`, in the form of its statement.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_factors_iff_of_isOpenSubspace`: an open
  subspace of a scheme, as a factorization criterion through an open subscheme.
* `AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple`: the relatively ample objects
  of the Picard stack have an open locus, given Stacks 0D3D.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism `T' ⟶ W` to the image of the terminal object of `𝒞/U`, which is the image of the
tautological morphism of an object `T` of `𝒞/U` up to the identifications of `T'` with the image
of `T` and of `W` with the image of the terminal object, factors through `v : V ⟶ W` if and only
if `T` maps to `V` read over `U`. -/
theorem exists_comp_eq_iff_nonempty_hom_overMk {𝒞 : Type*} [Category* 𝒞] {X : 𝒞} (U : Over X)
    {W V T' : Over X} (v : V ⟶ W) (hW : W = (Over.map U.hom).obj (Over.mk (𝟙 U.left)))
    (T : Over U.left) (h1 : T' = (Over.map U.hom).obj T) (b : T' ⟶ W)
    (hb : b = eqToHom h1 ≫ (Over.map U.hom).map
      (Over.homMk T.hom (Category.comp_id _) : T ⟶ Over.mk (𝟙 U.left)) ≫ eqToHom hW.symm) :
    (∃ k : T' ⟶ V, k ≫ v = b) ↔ Nonempty (T ⟶ Over.mk (v.left ≫ (eqToHom hW).left)) := by
  subst h1 hW hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Over.id_left]
  constructor
  · rintro ⟨k, hk⟩
    have h := congrArg CommaMorphism.left hk
    simp only [Over.comp_left, Over.map_map_left, Over.homMk_left] at h
    exact ⟨Over.homMk k.left (by simpa using h)⟩
  · rintro ⟨h⟩
    have hw : h.left ≫ v.left = T.hom := by simpa using Over.w h
    refine ⟨Over.homMk h.left ?_, ?_⟩
    · have hv := Over.w v
      simp only [Over.map_obj_hom, Over.mk_hom] at hv ⊢
      rw [← hv, ← Category.assoc, hw]
      exact congrArg (fun k => T.hom ≫ k) (Category.id_comp _)
    · ext
      simpa using hw

/-- **An open subspace of a scheme is cut out by an open subscheme**, in the form of a
factorization criterion: for an open subspace `G` of the presheaf represented by a scheme `W`,
there is a morphism `V ⟶ W` whose underlying morphism of schemes is an open immersion, such that
a morphism `T ⟶ W` factors through `V ⟶ W` if and only if the morphism of represented presheaves
factors through `G`. -/
theorem exists_isOpenImmersion_factors_iff_of_isOpenSubspace (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {W : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj W)) (hG : IsOpenSubspace B S hS G) :
    ∃ (V : BigFppfOver B S hS) (v : V ⟶ W),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
        ∀ {T : BigFppfOver B S hS} (t : T ⟶ W),
          (∃ k : T ⟶ V, k ≫ v = t) ↔ ∃ l : yoneda.obj T ⟶ G.toFunctor, l ≫ G.ι = yoneda.map t := by
  obtain ⟨V, v, e, hv, he⟩ := exists_openImmersion_of_isOpenSubspace B S hS W G hG
  refine ⟨V, v, hv, fun {T} t => ⟨?_, ?_⟩⟩
  · rintro ⟨k, rfl⟩
    exact ⟨yoneda.map k ≫ e.hom, by rw [Category.assoc, he, Functor.map_comp]⟩
  · rintro ⟨l, hl⟩
    refine ⟨yoneda.preimage (l ≫ e.inv), yoneda.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, Category.assoc, ← he, Iso.inv_hom_id_assoc, hl]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)

/-- **The relatively ample objects of the Picard stack have an open locus**, given Stacks 0D3D
as the hypothesis `h0D3D`. For a scheme-valued point `y` of `Picardstack_{X/Y}` with values in
`U` there is an open subscheme `V ⊆ U` such that a scheme `T ⟶ U` factors through `V` if and only
if the invertible module of `y(T)` is ample on `X_T/T`. -/
theorem hasOpenObjectPropertyLocus_picardAmple (hproper : IsProper B S hS s.f.hom)
    (h0D3D : ∀ {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}, IsProper B S hS f.hom →
      ∀ {L : Modules.{u, u} B S hS X.1 X.2}, IsInvertibleModule X L →
        ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
          ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
            IsPullback p f' f g →
              ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
                IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L))) :
    Stack.HasOpenObjectPropertyLocus B S hS (picardCFG hc s).val (picardAmple hc s) := by
  intro U y hy
  let A := y.obj (Over.mk (𝟙 _))
  have hpA : IsProper B S hS (baseChangeInclusion s.f A.T).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f
        ((schemesOverToOver s.base).obj A.T).hom) hproper
  obtain ⟨V, hV, hfac⟩ := h0D3D hpA A.invertible
  obtain ⟨V', v, hv, hvfac⟩ := exists_isOpenImmersion_factors_iff_of_isOpenSubspace B S hS V hV
  have hW : A.T.left = (Over.map U.hom).obj (Over.mk (𝟙 U.left)) := Functor.congr_obj hy _
  refine ⟨Over.mk (v.left ≫ (eqToHom hW).left), ?_, fun T => ?_⟩
  · have := hv
    change AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v ≫
      (BigFppfOver.toScheme B S hS).map (eqToHom hW))
    infer_instance
  · let t : T ⟶ Over.mk (𝟙 U.left) := Over.homMk T.hom (Category.comp_id _)
    let m := y.map t
    have key := hfac _ _ _ (isPullback_baseChangeMap s.f (PicardHom.base m))
    have hamp : IsRelativelyAmple B S hS (baseChangeInclusion s.f (y.obj T).T)
        ((modulePullback B S hS (baseChangeMap s.f (PicardHom.base m))).obj A.lineBundle) ↔
          picardAmple hc s (y.obj T) :=
      have := PicardHom.isIso_fibre m
      isRelativelyAmple_congr _ (asIso (PicardHom.fibre m))
    exact ((exists_comp_eq_iff_nonempty_hom_overMk U v hW T (Functor.congr_obj hy T) _
      (Functor.congr_hom hy t)).symm.trans (hvfac _)).trans (key.trans hamp)

end AlgebraicGeometry.Space

end
