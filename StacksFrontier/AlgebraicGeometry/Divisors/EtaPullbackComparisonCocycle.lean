module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComplex

/-!
# The comparison of décalages under pullback: naturality, the limit it measures, and a cocycle

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I ⊆ 𝒪_Y` an invertible ideal sheaf and `F^•` a
complex of `𝒪_Y`-modules. The canonical comparison

`f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•)`

of `Stacks.IdealTorsion.Eta.pullbackEtaMap` is assembled from the degreewise maps
`Stacks.IdealTorsion.Eta.pullbackEtaTermMap`. This file records three properties of it, none of
which needs flatness.

* It is natural in the complex: a map `a : F^• ⟶ G^•` of complexes of torsion-free modules gives
  a commutative square with `f^*(η_I a)` and `η_{f^*I}(f^*a)`.
* In each degree it is the comparison map `f^*(P) ⟶ f^*A ×_{f^*C} f^*B` of the fibre product
  `P = A ×_C B` defining the degree-`n` term of `η_I F^•`, followed by an isomorphism. So it is an
  isomorphism in degree `n` exactly when `f^*` preserves that fibre product.
* It satisfies a cocycle condition for a factorisation `k = q ∘ p` of morphisms of ringed spaces
  together with an isomorphism `β : p^* ∘ q^* ≅ k^*`: the composite
  `k^*(η_I F^•) ≅ p^*q^*(η_I F^•) ⟶ p^*(η_{q^*I}(q^*F^•)) ⟶ η_{p^*q^*I}(p^*q^*F^•)` is the
  comparison for `k` followed by an isomorphism of complexes
  `η_{k^*I}(k^*F^•) ≅ η_{p^*q^*I}(p^*q^*F^•)`. That isomorphism is built from the interchanges of
  pullbacks with ideal powers and from `β` alone, so the cocycle condition holds on the nose,
  with no compatibility of the interchanges with composition required.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso`: for `β : p^* ∘ q^* ≅ k^*`, the
  isomorphism `(k^*I)^{⊗ n} ⊗ k^*M ≅ (p^*q^*I)^{⊗ n} ⊗ p^*q^*M`.
* `Stacks.IdealTorsion.Eta.pullbackCompEtaIso`: the induced isomorphism of décalages
  `η_{k^*I}(k^*F^•) ≅ η_{p^*q^*I}(p^*q^*F^•)`.

## Main results

* `Stacks.IdealTorsion.Eta.pullbackEtaMap_naturality`: naturality in the complex.
* `Stacks.IdealTorsion.Eta.pullbackEtaTermMap_eq`: the degreewise comparison is
  `CategoryTheory.Limits.pullbackComparison` followed by an isomorphism of fibre products, and
  `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap_iff` the resulting criterion.
* `Stacks.IdealTorsion.Eta.pullbackEtaMap_cocycle`: the cocycle condition.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

/-! ### Naturality in the complex -/

section Naturality

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (pullbackIdealIncl f I ι)]

/-- The degree-`n` component of the map of décalages induced by a map of complexes, typed at the
fibre-product spelling `Stacks.IdealTorsion.Eta.etaTerm` of the terms. The component
`(etaMap Z J κ a hF hG).f n` is the same morphism, typed at the spelling `(etaObj ...).X n`, which
is not reducibly the fibre product; composites mixing the two spellings are rejected by `rw`. -/
private noncomputable def etaMapTerm (Z : RingedSpace.{u})
    (J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) [Mono κ]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property J]
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Z κ (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Z κ (G.X n)) (n : ℤ) :
    etaTerm Z J κ F n ⟶ etaTerm Z J κ G n :=
  (etaMap Z J κ a hF hG).f n

private theorem etaMapTerm_fst (Z : RingedSpace.{u})
    (J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) [Mono κ]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property J]
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Z κ (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Z κ (G.X n)) (n : ℤ) :
    etaMapTerm Z J κ a hF hG n ≫ etaFst Z J κ G n =
      etaFst Z J κ F n ≫ idealPowerMap Z J n (a.f n) :=
  etaMap_fst Z J κ a hF hG n

private theorem etaMapTerm_snd (Z : RingedSpace.{u})
    (J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) [Mono κ]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property J]
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Z κ (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Z κ (G.X n)) (n : ℤ) :
    etaMapTerm Z J κ a hF hG n ≫ etaSnd Z J κ G n =
      etaSnd Z J κ F n ≫ idealPowerMap Z J (n + 1) (a.f (n + 1)) :=
  etaMap_snd Z J κ a hF hG n

/-- The degreewise naturality of the comparison, at the fibre-product spelling. -/
private theorem pullbackEtaTermMap_naturality_aux
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n))
    (n : ℤ) :
    (pullbackFunctor f).map (etaMapTerm Y I ι a hF hG n) ≫ pullbackEtaTermMap f I ι G n =
      pullbackEtaTermMap f I ι F n ≫
        etaMapTerm X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) hF' hG' n := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullbackEtaTermMap_fst, Category.assoc,
      etaMapTerm_fst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) _ hF' hG' n,
      reassoc_of% (pullbackEtaTermMap_fst f I ι F n), ← Functor.map_comp_assoc,
      etaMapTerm_fst Y I ι a hF hG n, Functor.map_comp, Category.assoc,
      pullbackIdealPowerIso_natural]
    rfl
  · rw [Category.assoc, pullbackEtaTermMap_snd, Category.assoc,
      etaMapTerm_snd X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) _ hF' hG' n,
      reassoc_of% (pullbackEtaTermMap_snd f I ι F n), ← Functor.map_comp_assoc,
      etaMapTerm_snd Y I ι a hF hG n, Functor.map_comp, Category.assoc,
      pullbackIdealPowerIso_natural]
    rfl

/-- **The comparison of décalages is natural in the complex**: for a map `a : F^• ⟶ G^•` of
complexes of `I`-torsion-free modules whose pullbacks are `f^*I`-torsion-free, the square formed
by `f^*(η_I a)`, `η_{f^*I}(f^*a)` and the two comparisons commutes. -/
theorem pullbackEtaMap_naturality
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n)) :
    ((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map (etaMap Y I ι a hF hG) ≫
        pullbackEtaMap f I ι G hG hG' =
      pullbackEtaMap f I ι F hF hF' ≫
        etaMap X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) hF' hG' := by
  ext n : 1
  exact pullbackEtaTermMap_naturality_aux f I ι a hF hG hF' hG' n

end Naturality

/-! ### The degreewise comparison is a comparison of fibre products -/

section Comparison

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (n : ℤ)

/-- The isomorphism between the fibre product of the pulled-back cospan defining the degree-`n`
term of `η_I F^•` and the degree-`n` term of `η_{f^*I}(f^*F^•)`, induced by the interchanges of
the pullback with the ideal powers. -/
noncomputable def pullbackEtaCospanIso :
    pullback ((pullbackFunctor f).map (idealPowerMap Y I n (F.d n (n + 1))))
        ((pullbackFunctor f).map (idealPowerIncl Y I ι n (F.X (n + 1)))) ≅
      etaTerm X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n :=
  asIso (pullback.map _ _
    (idealPowerMap X ((pullbackFunctor f).obj I) n ((pullbackFunctor f).map (F.d n (n + 1))))
    (idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
      ((pullbackFunctor f).obj (F.X (n + 1))))
    (pullbackIdealPowerIso f I n (F.X n)).hom
    (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom
    (pullbackIdealPowerIso f I n (F.X (n + 1))).hom
    (pullbackIdealPowerIso_natural f I n (F.d n (n + 1)))
    (map_idealPowerIncl f I ι n (F.X (n + 1))))

/-- `Stacks.IdealTorsion.Eta.pullbackEtaCospanIso` followed by the first projection of
`η_{f^*I}(f^*F^•)` in degree `n` is the first projection followed by the interchange
`Stacks.IdealTorsion.Eta.pullbackIdealPowerIso` in degree `n`. -/
theorem pullbackEtaCospanIso_hom_fst :
    (pullbackEtaCospanIso f I ι F n).hom ≫
        etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n =
      pullback.fst _ _ ≫ (pullbackIdealPowerIso f I n (F.X n)).hom :=
  pullback.lift_fst _ _ _

/-- `Stacks.IdealTorsion.Eta.pullbackEtaCospanIso` followed by the second projection of
`η_{f^*I}(f^*F^•)` in degree `n` is the second projection followed by the interchange
`Stacks.IdealTorsion.Eta.pullbackIdealPowerIso` in degree `n + 1`. -/
theorem pullbackEtaCospanIso_hom_snd :
    (pullbackEtaCospanIso f I ι F n).hom ≫
        etaSnd X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n =
      pullback.snd _ _ ≫ (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom :=
  pullback.lift_snd _ _ _

/-- **The degreewise comparison of décalages is the comparison map of a fibre product**: it is
`CategoryTheory.Limits.pullbackComparison` for `f^*` at the cospan defining the degree-`n` term
of `η_I F^•`, followed by `Stacks.IdealTorsion.Eta.pullbackEtaCospanIso`. -/
theorem pullbackEtaTermMap_eq :
    pullbackEtaTermMap f I ι F n =
      pullbackComparison (pullbackFunctor f) (idealPowerMap Y I n (F.d n (n + 1)))
          (idealPowerIncl Y I ι n (F.X (n + 1))) ≫
        (pullbackEtaCospanIso f I ι F n).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackEtaTermMap_fst, Category.assoc, pullbackEtaCospanIso_hom_fst, ← Category.assoc,
      pullbackComparison_comp_fst]
  · rw [pullbackEtaTermMap_snd, Category.assoc, pullbackEtaCospanIso_hom_snd, ← Category.assoc,
      pullbackComparison_comp_snd]

/-- The degreewise comparison of décalages is an isomorphism exactly when `f^*` preserves the
fibre product defining the degree-`n` term of `η_I F^•`. -/
theorem isIso_pullbackEtaTermMap_iff :
    IsIso (pullbackEtaTermMap f I ι F n) ↔
      IsIso (pullbackComparison (pullbackFunctor f) (idealPowerMap Y I n (F.d n (n + 1)))
        (idealPowerIncl Y I ι n (F.X (n + 1)))) := by
  rw [pullbackEtaTermMap_eq]
  exact ⟨fun _ => IsIso.of_isIso_comp_right _ (pullbackEtaCospanIso f I ι F n).hom,
    fun _ => inferInstance⟩

end Comparison

/-! ### The cocycle condition -/

section Cocycle

variable {X Y Z : RingedSpace.{u}} (p : X ⟶ Y) (q : Y ⟶ Z) (k : X ⟶ Z)
  (β : pullbackFunctor q ⋙ pullbackFunctor p ≅ pullbackFunctor k)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
  [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property I]

/-- For an isomorphism `β : p^* ∘ q^* ≅ k^*`, the identification
`(k^*I)^{⊗ n} ⊗ k^*M ≅ (p^*q^*I)^{⊗ n} ⊗ p^*q^*M` obtained by moving each pullback out of the
ideal power, applying `β`, and moving the pullbacks back in. -/
noncomputable def pullbackCompIdealPowerIso (n : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    idealPowerTerm X ((pullbackFunctor k).obj I) n ((pullbackFunctor k).obj M) ≅
      idealPowerTerm X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I)) n
        ((pullbackFunctor p).obj ((pullbackFunctor q).obj M)) :=
  (pullbackIdealPowerIso k I n M).symm ≪≫ (β.app (idealPowerTerm Z I n M)).symm ≪≫
    (pullbackFunctor p).mapIso (pullbackIdealPowerIso q I n M) ≪≫
    pullbackIdealPowerIso p ((pullbackFunctor q).obj I) n ((pullbackFunctor q).obj M)

/-- A map between ideal-power terms commutes with
`Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso` as soon as its pullbacks along `k`, `q` and `p`
commute with the interchange isomorphisms. -/
private theorem pullbackCompIdealPowerIso_comm {n n' : ℤ}
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)}
    {g : idealPowerTerm Z I n M ⟶ idealPowerTerm Z I n' N}
    {gk : idealPowerTerm X ((pullbackFunctor k).obj I) n ((pullbackFunctor k).obj M) ⟶
      idealPowerTerm X ((pullbackFunctor k).obj I) n' ((pullbackFunctor k).obj N)}
    {gq : idealPowerTerm Y ((pullbackFunctor q).obj I) n ((pullbackFunctor q).obj M) ⟶
      idealPowerTerm Y ((pullbackFunctor q).obj I) n' ((pullbackFunctor q).obj N)}
    {gp : idealPowerTerm X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I)) n
        ((pullbackFunctor p).obj ((pullbackFunctor q).obj M)) ⟶
      idealPowerTerm X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I)) n'
        ((pullbackFunctor p).obj ((pullbackFunctor q).obj N))}
    (hk : (pullbackFunctor k).map g ≫ (pullbackIdealPowerIso k I n' N).hom =
      (pullbackIdealPowerIso k I n M).hom ≫ gk)
    (hq : (pullbackFunctor q).map g ≫ (pullbackIdealPowerIso q I n' N).hom =
      (pullbackIdealPowerIso q I n M).hom ≫ gq)
    (hp : (pullbackFunctor p).map gq ≫
        (pullbackIdealPowerIso p ((pullbackFunctor q).obj I) n' ((pullbackFunctor q).obj N)).hom =
      (pullbackIdealPowerIso p ((pullbackFunctor q).obj I) n ((pullbackFunctor q).obj M)).hom ≫
        gp) :
    gk ≫ (pullbackCompIdealPowerIso p q k β I n' N).hom =
      (pullbackCompIdealPowerIso p q k β I n M).hom ≫ gp := by
  have h1 : gk ≫ (pullbackIdealPowerIso k I n' N).inv =
      (pullbackIdealPowerIso k I n M).inv ≫ (pullbackFunctor k).map g := by
    rw [Iso.comp_inv_eq, Category.assoc, hk, Iso.inv_hom_id_assoc]
  have h2 := β.inv.naturality g
  have h3 : (pullbackFunctor p).map ((pullbackFunctor q).map g) ≫
      (pullbackFunctor p).map (pullbackIdealPowerIso q I n' N).hom =
        (pullbackFunctor p).map (pullbackIdealPowerIso q I n M).hom ≫
          (pullbackFunctor p).map gq := by
    rw [← Functor.map_comp, ← Functor.map_comp, hq]
  simp only [pullbackCompIdealPowerIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_inv, Category.assoc]
  rw [reassoc_of% h1]
  simp only [Functor.comp_obj, Functor.comp_map] at h2
  rw [reassoc_of% h2, reassoc_of% h3, hp]

/-- `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso` is natural in the module. -/
theorem pullbackCompIdealPowerIso_natural (n : ℤ)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)} (a : M ⟶ N) :
    idealPowerMap X ((pullbackFunctor k).obj I) n ((pullbackFunctor k).map a) ≫
        (pullbackCompIdealPowerIso p q k β I n N).hom =
      (pullbackCompIdealPowerIso p q k β I n M).hom ≫
        idealPowerMap X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I)) n
          ((pullbackFunctor p).map ((pullbackFunctor q).map a)) :=
  pullbackCompIdealPowerIso_comm p q k β I (pullbackIdealPowerIso_natural k I n a)
    (pullbackIdealPowerIso_natural q I n a)
    (pullbackIdealPowerIso_natural p ((pullbackFunctor q).obj I) n ((pullbackFunctor q).map a))

/-- `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso` respects the inclusions of consecutive
ideal powers. -/
theorem pullbackCompIdealPowerIso_idealPowerIncl (n : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    idealPowerIncl X ((pullbackFunctor k).obj I) (pullbackIdealIncl k I ι) n
          ((pullbackFunctor k).obj M) ≫ (pullbackCompIdealPowerIso p q k β I n M).hom =
      (pullbackCompIdealPowerIso p q k β I (n + 1) M).hom ≫
        idealPowerIncl X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I))
          (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)) n
          ((pullbackFunctor p).obj ((pullbackFunctor q).obj M)) :=
  pullbackCompIdealPowerIso_comm p q k β I (map_idealPowerIncl k I ι n M)
    (map_idealPowerIncl q I ι n M)
    (map_idealPowerIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι) n
      ((pullbackFunctor q).obj M))

variable
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ)

/-- The degree-`n` component of `Stacks.IdealTorsion.Eta.pullbackCompEtaIso`: the map of fibre
products induced by `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso`. -/
noncomputable def pullbackCompEtaTermMap (n : ℤ) :
    etaTerm X ((pullbackFunctor k).obj I) (pullbackIdealIncl k I ι) (pullbackComplex k F) n ⟶
      etaTerm X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I))
        (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
        (pullbackComplex p (pullbackComplex q F)) n :=
  pullback.map _ _ _ _ (pullbackCompIdealPowerIso p q k β I n (F.X n)).hom
    (pullbackCompIdealPowerIso p q k β I (n + 1) (F.X (n + 1))).hom
    (pullbackCompIdealPowerIso p q k β I n (F.X (n + 1))).hom
    (pullbackCompIdealPowerIso_natural p q k β I n (F.d n (n + 1)))
    (pullbackCompIdealPowerIso_idealPowerIncl p q k β I ι n (F.X (n + 1)))

/-- `Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap` is an isomorphism. -/
theorem isIso_pullbackCompEtaTermMap (n : ℤ) : IsIso (pullbackCompEtaTermMap p q k β I ι F n) := by
  dsimp only [pullbackCompEtaTermMap]
  infer_instance

/-- `Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap` followed by the first projection is the
first projection followed by `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso` in degree `n`. -/
theorem pullbackCompEtaTermMap_fst (n : ℤ) :
    pullbackCompEtaTermMap p q k β I ι F n ≫
        etaFst X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I))
          (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
          (pullbackComplex p (pullbackComplex q F)) n =
      etaFst X ((pullbackFunctor k).obj I) (pullbackIdealIncl k I ι) (pullbackComplex k F) n ≫
        (pullbackCompIdealPowerIso p q k β I n (F.X n)).hom :=
  pullback.lift_fst _ _ _

/-- `Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap` followed by the second projection is the
second projection followed by `Stacks.IdealTorsion.Eta.pullbackCompIdealPowerIso` in degree
`n + 1`. -/
theorem pullbackCompEtaTermMap_snd (n : ℤ) :
    pullbackCompEtaTermMap p q k β I ι F n ≫
        etaSnd X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I))
          (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
          (pullbackComplex p (pullbackComplex q F)) n =
      etaSnd X ((pullbackFunctor k).obj I) (pullbackIdealIncl k I ι) (pullbackComplex k F) n ≫
        (pullbackCompIdealPowerIso p q k β I (n + 1) (F.X (n + 1))).hom :=
  pullback.lift_snd _ _ _

/-- **The cocycle condition, degreewise.** The comparison along `q` pulled back along `p`,
followed by the comparison along `p`, is the comparison along `k` followed by
`Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap`, after the identification `β`. -/
theorem pullbackEtaTermMap_cocycle (n : ℤ) :
    β.inv.app (etaTerm Z I ι F n) ≫ (pullbackFunctor p).map (pullbackEtaTermMap q I ι F n) ≫
        pullbackEtaTermMap p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)
          (pullbackComplex q F) n =
      pullbackEtaTermMap k I ι F n ≫ pullbackCompEtaTermMap p q k β I ι F n := by
  refine pullback.hom_ext ?_ ?_
  · have h := β.inv.naturality (etaFst Z I ι F n)
    simp only [Functor.comp_obj, Functor.comp_map] at h
    rw [Category.assoc, Category.assoc, pullbackEtaTermMap_fst, ← Functor.map_comp_assoc,
      pullbackEtaTermMap_fst, Category.assoc, pullbackCompEtaTermMap_fst,
      reassoc_of% (pullbackEtaTermMap_fst k I ι F n)]
    simp only [pullbackCompIdealPowerIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_inv, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
    rw [reassoc_of% h]
    rfl
  · have h := β.inv.naturality (etaSnd Z I ι F n)
    simp only [Functor.comp_obj, Functor.comp_map] at h
    rw [Category.assoc, Category.assoc, pullbackEtaTermMap_snd, ← Functor.map_comp_assoc,
      pullbackEtaTermMap_snd, Category.assoc, pullbackCompEtaTermMap_snd,
      reassoc_of% (pullbackEtaTermMap_snd k I ι F n)]
    simp only [pullbackCompIdealPowerIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_inv, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
    rw [reassoc_of% h]
    rfl

variable [Mono ι] [Mono (pullbackIdealIncl k I ι)] [Mono (pullbackIdealIncl q I ι)]
  [Mono (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))]

omit [Mono ι] [Mono (pullbackIdealIncl q I ι)] in
/-- `Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap` commutes with the differentials of the two
décalages, at the fibre-product spelling of their terms. -/
theorem pullbackCompEtaTermMap_comm
    (hk : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl k I ι) ((pullbackComplex k F).X n))
    (hpq : ∀ n : ℤ, IsIdealTorsionFree X
      (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
      ((pullbackComplex p (pullbackComplex q F)).X n)) (i : ℤ) :
    pullbackCompEtaTermMap p q k β I ι F i ≫ (etaDifferentialData X _ _ _ hpq).d i =
      (etaDifferentialData X _ _ _ hk).d i ≫ pullbackCompEtaTermMap p q k β I ι F (i + 1) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, (etaDifferentialData X _ _ _ hpq).d_fst i,
      pullbackCompEtaTermMap_snd, pullbackCompEtaTermMap_fst, ← Category.assoc,
      (etaDifferentialData X _ _ _ hk).d_fst i]
  · rw [Category.assoc, Category.assoc, etaDifferentialData_d_comp_etaSnd X _ _ _ hpq i,
      comp_zero, pullbackCompEtaTermMap_snd, ← Category.assoc,
      etaDifferentialData_d_comp_etaSnd X _ _ _ hk i, zero_comp]

/-- **The isomorphism of décalages `η_{k^*I}(k^*F^•) ≅ η_{p^*q^*I}(p^*q^*F^•)`** induced by
`β : p^* ∘ q^* ≅ k^*`, degreewise `Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap`. -/
noncomputable def pullbackCompEtaIso
    (hk : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl k I ι) ((pullbackComplex k F).X n))
    (hpq : ∀ n : ℤ, IsIdealTorsionFree X
      (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
      ((pullbackComplex p (pullbackComplex q F)).X n)) :
    etaObj X ((pullbackFunctor k).obj I) (pullbackIdealIncl k I ι) (pullbackComplex k F) hk ≅
      etaObj X ((pullbackFunctor p).obj ((pullbackFunctor q).obj I))
        (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
        (pullbackComplex p (pullbackComplex q F)) hpq :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => @asIso _ _ _ _ (pullbackCompEtaTermMap p q k β I ι F n)
      (isIso_pullbackCompEtaTermMap p q k β I ι F n)) (by
      rintro i j (rfl : i + 1 = j)
      rw [etaObj_d_eq, etaObj_d_eq]
      exact pullbackCompEtaTermMap_comm p q k β I ι F hk hpq i)

omit [Mono ι] [Mono (pullbackIdealIncl q I ι)] in
/-- The degree-`n` component of `Stacks.IdealTorsion.Eta.pullbackCompEtaIso` is
`Stacks.IdealTorsion.Eta.pullbackCompEtaTermMap`. -/
theorem pullbackCompEtaIso_hom_f
    (hk : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl k I ι) ((pullbackComplex k F).X n))
    (hpq : ∀ n : ℤ, IsIdealTorsionFree X
      (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
      ((pullbackComplex p (pullbackComplex q F)).X n)) (n : ℤ) :
    (pullbackCompEtaIso p q k β I ι F hk hpq).hom.f n = pullbackCompEtaTermMap p q k β I ι F n :=
  rfl

/-- **The cocycle condition for the comparison of décalages.** For a factorisation `k = q ∘ p`
witnessed by `β : p^* ∘ q^* ≅ k^*`, the composite
`k^*(η_I F^•) ≅ p^*q^*(η_I F^•) ⟶ p^*(η_{q^*I}(q^*F^•)) ⟶ η_{p^*q^*I}(p^*q^*F^•)` is the
comparison along `k` followed by `Stacks.IdealTorsion.Eta.pullbackCompEtaIso`. -/
theorem pullbackEtaMap_cocycle
    (hF : ∀ n : ℤ, IsIdealTorsionFree Z ι (F.X n))
    (hq : ∀ n : ℤ, IsIdealTorsionFree Y (pullbackIdealIncl q I ι) ((pullbackComplex q F).X n))
    (hk : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl k I ι) ((pullbackComplex k F).X n))
    (hpq : ∀ n : ℤ, IsIdealTorsionFree X
      (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
      ((pullbackComplex p (pullbackComplex q F)).X n)) :
    (Functor.mapHomologicalComplexCompIso β (ComplexShape.up ℤ)).inv.app (etaObj Z I ι F hF) ≫
        ((pullbackFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullbackEtaMap q I ι F hF hq) ≫
        pullbackEtaMap p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)
          (pullbackComplex q F) hq hpq =
      pullbackEtaMap k I ι F hF hk ≫ (pullbackCompEtaIso p q k β I ι F hk hpq).hom := by
  ext n : 1
  exact pullbackEtaTermMap_cocycle p q k β I ι F n

end Cocycle

end Stacks.IdealTorsion.Eta

end
