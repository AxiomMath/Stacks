module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackKFlatComparison

/-!
# The comparison of décalages under a composite of pullbacks, on quasi-isomorphisms

Let `g : W ⟶ X` and `f : X ⟶ Y` be morphisms of ringed spaces and `r : R^• ⟶ η_I F^•` a map of
complexes of `𝒪_Y`-modules.  This file shows that the map of complexes

`(g ≫ f)^* R^• ⟶ (g ≫ f)^*(η_I F^•) ⟶ η_K((g ≫ f)^* F^•)`

built from the comparison of décalages for the composite is a quasi-isomorphism exactly when the
map

`g^*(f^* R^•) ⟶ g^*(η_J(f^* F^•)) ⟶ η_K(g^* f^* F^•)`

built from the comparisons for `f` and for `g` is one.  The two differ by the
pullback-composition isomorphisms and by the automorphism of the target of
`Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_comp`.

## Main results

* `Stacks.IdealTorsion.Eta.quasiIso_transportedPullbackEtaMap_comp_iff`.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

/-- The termwise pullback of a composite of maps of complexes. -/
theorem pullbackComplexMap_comp {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    pullbackComplexMap f (φ ≫ ψ) = pullbackComplexMap f φ ≫ pullbackComplexMap f ψ :=
  ((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map_comp φ ψ

/-- The décalage of an isomorphism of complexes of torsion-free modules, as an isomorphism. -/
def etaMapIso (Z : RingedSpace.{u})
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    (μ : L ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) [Mono μ]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property L]
    {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ}
    (e : K ≅ M) (hK : ∀ n : ℤ, IsIdealTorsionFree Z μ (K.X n))
    (hM : ∀ n : ℤ, IsIdealTorsionFree Z μ (M.X n)) :
    etaObj Z L μ K hK ≅ etaObj Z L μ M hM where
  hom := etaMap Z L μ e.hom hK hM
  inv := etaMap Z L μ e.inv hM hK
  hom_inv_id := by rw [← etaMap_comp, e.hom_inv_id, etaMap_id]
  inv_hom_id := by rw [← etaMap_comp, e.inv_hom_id, etaMap_id]

section Composite

variable {W X Y : RingedSpace.{u}} (g : W ⟶ X) (f : X ⟶ Y)
  {I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
  {ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  {J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
  {κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)}
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property J]
  {K : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)}
  {κ' : K ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf)}
  [Stacks.SheafOfModules.IsInvertible W.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf).property K]
  [Mono ι] [Mono κ] [Mono κ']
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    (pullbackIdealIncl g J κ)]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    (pullbackIdealIncl (g ≫ f) I ι)]
  (ef : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackFunctor f).obj I) J) (hef : ef.hom ≫ κ = pullbackIdealIncl f I ι)
  (eg : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    ((pullbackFunctor g).obj J) K) (heg : eg.hom ≫ κ' = pullbackIdealIncl g J κ)
  (egf : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    ((pullbackFunctor (g ≫ f)).obj I) K) (hegf : egf.hom ≫ κ' = pullbackIdealIncl (g ≫ f) I ι)
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hFf' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
  (hFf : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f F).X n))
  (hFg' : ∀ n : ℤ, IsIdealTorsionFree W (pullbackIdealIncl g J κ)
    ((pullbackComplex g (pullbackComplex f F)).X n))
  (hFg : ∀ n : ℤ, IsIdealTorsionFree W κ' ((pullbackComplex g (pullbackComplex f F)).X n))
  (hFgf' : ∀ n : ℤ, IsIdealTorsionFree W (pullbackIdealIncl (g ≫ f) I ι)
    ((pullbackComplex (g ≫ f) F).X n))
  (hFgf : ∀ n : ℤ, IsIdealTorsionFree W κ' ((pullbackComplex (g ≫ f) F).X n))

/-- The pullback-composition isomorphism is natural in the complex. -/
theorem pullbackComplexCompIso_naturality
    {L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (φ : L ⟶ M) :
    pullbackComplexMap (g ≫ f) φ ≫ (pullbackComplexCompIso g f M).hom =
      (pullbackComplexCompIso g f L).hom ≫ pullbackComplexMap g (pullbackComplexMap f φ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact pullbackCompIso_natural g f (φ.f n)

/-- **The comparison of décalages for a composite, precomposed with the pullback of a map of
complexes, is a quasi-isomorphism exactly when the composite of the comparisons for the two
factors is.** -/
theorem quasiIso_transportedPullbackEtaMap_comp_iff
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (r : R ⟶ etaObj Y I ι F hF) :
    QuasiIso (pullbackComplexMap (g ≫ f) r ≫
        transportedPullbackEtaMap (g ≫ f) I ι K κ' egf hegf F hF hFgf' hFgf) ↔
      QuasiIso (pullbackComplexMap g (pullbackComplexMap f r ≫
          transportedPullbackEtaMap f I ι J κ ef hef F hF hFf' hFf) ≫
        transportedPullbackEtaMap g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg) := by
  set σ := ((PowerInterchange.twist F (transportInterchange (g ≫ f) I ι K κ' egf hegf)
    ((transportInterchange f I ι J κ ef hef).comp
      (transportInterchange g J κ K κ' eg heg))).iso hFgf)
  set c := etaMapIso W K κ' (pullbackComplexCompIso g f F).symm hFg hFgf
  have key : pullbackComplexMap (g ≫ f) r ≫
      transportedPullbackEtaMap (g ≫ f) I ι K κ' egf hegf F hF hFgf' hFgf =
      (pullbackComplexCompIso g f R).hom ≫
        (pullbackComplexMap g (pullbackComplexMap f r ≫
          transportedPullbackEtaMap f I ι J κ ef hef F hF hFf' hFf) ≫
        transportedPullbackEtaMap g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg) ≫
        c.hom ≫ σ.hom := by
    rw [transportedPullbackEtaMap_comp g f ef hef eg heg egf hegf F hF hFf' hFf hFg' hFg
      hFgf' hFgf, compositePullbackEtaMap]
    simp only [Category.assoc]
    rw [← Category.assoc (pullbackComplexMap (g ≫ f) r), pullbackComplexCompIso_naturality,
      pullbackComplexMap_comp]
    simp only [Category.assoc]
    rfl
  rw [key, quasiIso_iff_comp_left, ← Category.assoc, quasiIso_iff_comp_right,
    quasiIso_iff_comp_right]

omit [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
    (pullbackIdealIncl (g ≫ f) I ι)] in
/-- `Stacks.IdealTorsion.Eta.quasiIso_transportedPullbackEtaMap_comp_iff`, with the composite
morphism given as an arbitrary morphism `k` equal to `g ≫ f`.  This is the form in which it is
applied to a composite of morphisms of schemes, whose underlying morphism of ringed spaces is the
composite only up to an equation. -/
theorem quasiIso_transportedPullbackEtaMap_comp_iff' (k : W ⟶ Y) (hk : g ≫ f = k)
    [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
      (pullbackIdealIncl k I ι)]
    (ek : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))
      ((pullbackFunctor k).obj I) K) (hek : ek.hom ≫ κ' = pullbackIdealIncl k I ι)
    (hFk' : ∀ n : ℤ, IsIdealTorsionFree W (pullbackIdealIncl k I ι)
      ((pullbackComplex k F).X n))
    (hFk : ∀ n : ℤ, IsIdealTorsionFree W κ' ((pullbackComplex k F).X n))
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (r : R ⟶ etaObj Y I ι F hF) :
    QuasiIso (pullbackComplexMap k r ≫
        transportedPullbackEtaMap k I ι K κ' ek hek F hF hFk' hFk) ↔
      QuasiIso (pullbackComplexMap g (pullbackComplexMap f r ≫
          transportedPullbackEtaMap f I ι J κ ef hef F hF hFf' hFf) ≫
        transportedPullbackEtaMap g J κ K κ' eg heg (pullbackComplex f F) hFf hFg' hFg) := by
  subst hk
  exact quasiIso_transportedPullbackEtaMap_comp_iff g f ef hef eg heg ek hek F hF hFf' hFf hFg'
    hFg hFk' hFk r

end Composite

end Stacks.IdealTorsion.Eta

end
