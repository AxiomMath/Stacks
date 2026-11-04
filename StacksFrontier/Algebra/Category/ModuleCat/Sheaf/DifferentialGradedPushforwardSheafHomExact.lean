module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConcreteDGFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInternalHomModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRightDerivedExtension

/-!
# The exact functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of homotopy categories

Let `f` be a morphism of ringed sites, let `𝒜` and `𝒜'` be sheaves of differential graded
algebras on its source, let `ℬ` be one on its target, let `φ : ℬ ⟶ f_*𝒜` be a homomorphism and
let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. The functor

`Mod(𝒜', d) ⥤ Mod(ℬ, d)`, `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`

extends to homogeneous maps: the internal hom postcomposes, and the direct image is applied
degreewise. So it is a functor of differential graded categories, and by
[Stacks, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF) in the additive form of
`DGCategory.AddDGFunctor.isTriangulated` it induces an exact functor

`K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`

of triangulated categories. This is [Stacks, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
for a morphism of ringed sites given by a continuous functor of the underlying sites.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor.comp`: the composite of two
  functors extended to homogeneous maps.
* `SheafOfModules.DifferentialGradedModule.pushforwardConcreteDGFunctor`: the direct image,
  extended to homogeneous maps degreewise.
* `SheafOfModules.DifferentialGradedModule.sheafHomConcreteDGFunctor`: the internal hom
  `SheafHom^dg_{𝒜'}(𝒩, -)`, extended to homogeneous maps by postcomposition.
* `SheafOfModules.DifferentialGradedModule.pushforwardSheafHomConcreteDGFunctor`: their
  composite, the functor of the tag.
* `SheafOfModules.DifferentialGradedModule.homotopyPushforwardSheafHom`: the induced functor of
  homotopy categories, with its `Functor.CommShift ℤ` and `Functor.IsTriangulated` instances.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_isTriangulated_homotopyPushforwardSheafHom`:
  the exact functor of triangulated homotopy categories, along a continuous functor of sites;
  the statement along a morphism of ringed topoi is in
  `DifferentialGradedToposPushforwardSheafHomExact.lean`.
* `SheafOfModules.DifferentialGradedModule.exists_rightDerived_homotopyPushforwardSheafHom`:
  its right derived extension `D(𝒜', d) ⥤ D(ℬ, d)`.

## References

* [Stacks Project, Tag 0FTS](https://stacks.math.columbia.edu/tag/0FTS)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

universe u v v' v'' w w' w'' a a' z s

namespace AlgebraicGeometry.RingedSite

/-- The rings of sections of the sheaf of rings of a ringed site are commutative. -/
instance instIsMulCommutativeRingSheafObj (X : RingedSite.{u, u, u}) (U : X.Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := X.O.obj.obj U) a b⟩⟩

end AlgebraicGeometry.RingedSite

namespace SheafOfModules

/-! ### Linear cochains -/

section Linear

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- The two formulations of linearity of a cochain for the right action agree. -/
theorem DifferentialGradedModule.isActionLinear_iff {M N : DifferentialGradedModule.{u, v, w} A}
    {k : ℤ} (c : Cochain M.complex N.complex k) :
    DifferentialGradedModule.IsActionLinear A c ↔ CochainIsLinear c :=
  ⟨fun h p q m hpq U x b => eq_of_heq (h p q m hpq U x b),
    fun h p q m hpq U x b => heq_of_eq (h p q m hpq U x b)⟩

variable {K : DifferentialGradedModule.{u, v, z} A}

/-- Morphisms between the pieces of internal homs are equal if they agree on local sections. -/
private theorem hom_ext_local {L L' : DifferentialGradedModule.{u, v, s} A} {p q : ℤ}
    {F G : (sheafHomComplex K L).X p ⟶ (sheafHomComplex K L').X q}
    (h : ∀ (U : X.C) (f : ↑(((sheafHomComplex K L).X p).val.obj (Opposite.op U))) (i j : ℤ)
      (hij : i + q = j) (V : Over U) (x : ↑((K.complex.X i).val.obj (Opposite.op V.left))),
      (((homSections F (Opposite.op U)) f).app i j hij V) x =
        (((homSections G (Opposite.op U)) f).app i j hij V) x) :
    F = G := by
  refine hom_ext_sections fun U f => ?_
  induction U using Opposite.rec with | op U => exact LocalHom.ext (h U f)

/-- Postcomposition is additive in the cochain. -/
theorem sheafHomCochain_add {L L' : DifferentialGradedModule.{u, v, s} A} {k : ℤ}
    (c c' : Cochain L.complex L'.complex k) (hc : CochainIsLinear c)
    (hc' : CochainIsLinear c') (hcc' : CochainIsLinear (c + c')) :
    sheafHomCochain (K := K) (c + c') hcc' = sheafHomCochain c hc + sheafHomCochain c' hc' := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.add_v, sheafHomCochain_v, sheafHomCochain_v, sheafHomCochain_v]
  refine hom_ext_local fun U f i j hij V x => ?_
  rw [homSections_add, homSections_postcompHom, homSections_postcompHom,
    homSections_postcompHom, LocalHom.add_app, LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl,
    LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl,
    LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl, Cochain.add_v, ← homSections_apply,
    homSections_add]
  rfl

/-- Postcomposition with a composite of cochains is the composite of the postcompositions. -/
theorem sheafHomCochain_comp {L L' L'' : DifferentialGradedModule.{u, v, s} A} {k l m : ℤ}
    (c : Cochain L.complex L'.complex k) (c' : Cochain L'.complex L''.complex l) (h : k + l = m)
    (hc : CochainIsLinear c) (hc' : CochainIsLinear c') (hcc' : CochainIsLinear (c.comp c' h)) :
    sheafHomCochain (K := K) (c.comp c' h) hcc' =
      (sheafHomCochain c hc).comp (sheafHomCochain c' hc') h := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.comp_v _ _ h p (p + k) q rfl (by omega), sheafHomCochain_v, sheafHomCochain_v,
    sheafHomCochain_v]
  refine hom_ext_local fun U f i j hij V x => ?_
  rw [homSections_comp, homSections_postcompHom, homSections_postcompHom,
    homSections_postcompHom, LocalHom.postcomp_app _ _ _ _ i j hij (i + p) rfl,
    LocalHom.postcomp_app _ _ _ _ i j hij (i + p + k) (by omega),
    LocalHom.postcomp_app _ _ _ _ i (i + p + k) (by omega) (i + p) rfl,
    Cochain.comp_v _ _ h (i + p) (i + p + k) j rfl (by omega)]
  rfl

end Linear

namespace DifferentialGradedModule

/-! ### Composites -/

namespace ConcreteDGFunctor

variable {X Y Z : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, v'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  {C : DifferentialGradedAlgebra.{u, v''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}

/-- **The composite of two functors extended to homogeneous maps.** -/
noncomputable def comp (G : ConcreteDGFunctor.{u, v, v', w, w'} A B)
    (H : ConcreteDGFunctor.{u, v', v'', w', w''} B C) :
    ConcreteDGFunctor.{u, v, v'', w, w''} A C where
  functor := G.functor ⋙ H.functor
  mapCochain c hc := H.mapCochain (G.mapCochain c hc) (G.isActionLinear_mapCochain c hc)
  isActionLinear_mapCochain c hc := H.isActionLinear_mapCochain _ _
  mapCochain_add c c' hc hc' hcc' := by
    rw [H.mapCochain_congr (G.mapCochain_add c c' hc hc' hcc') _
      (actionLinear_add B _ _ (G.isActionLinear_mapCochain c hc)
        (G.isActionLinear_mapCochain c' hc')), H.mapCochain_add]
  mapCochain_delta c hc hδ := by
    rw [H.mapCochain_congr (G.mapCochain_delta c hc hδ) _
      (actionLinear_delta B _ (G.isActionLinear_mapCochain c hc)), H.mapCochain_delta]
  mapCochain_comp c c' h hc hc' hcc' := by
    rw [H.mapCochain_congr (G.mapCochain_comp c c' h hc hc' hcc') _
      (actionLinear_comp B _ _ _ (G.isActionLinear_mapCochain c hc)
        (G.isActionLinear_mapCochain c' hc')), H.mapCochain_comp]
  mapCochain_ofHom f := by
    rw [H.mapCochain_congr (G.mapCochain_ofHom f) _ (actionLinear_ofHom B _),
      H.mapCochain_ofHom]
    rfl

end ConcreteDGFunctor

/-! ### The direct image and the internal hom -/

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}} {f : Y.C ⥤ X.C} [f.IsContinuous Y.J X.J]
  {σ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
    f.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {A A' : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, a'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

/-- **The direct image, extended to homogeneous maps**: a cochain is pushed forward degreewise. -/
noncomputable def pushforwardConcreteDGFunctor
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A) :
    ConcreteDGFunctor.{u, a, a', w, w} A B where
  functor := pushforwardFunctor φ
  mapCochain c _ := c.map (sitePushforward f σ)
  isActionLinear_mapCochain _ hc p q m hpq V x b := hc p q m hpq (f.op.obj V) x (φ.app m V b)
  mapCochain_add _ _ _ _ _ := Cochain.map_add _ _ _
  mapCochain_delta _ _ _ := (δ_map _ _ _ _).symm
  mapCochain_comp c c' h _ _ _ :=
    Cochain.map_comp (z₁ := c) (z₂ := c') (h := h) (Φ := sitePushforward f σ) ..
  mapCochain_ofHom g := Cochain.map_ofHom _ _ g.toHomologicalComplex _

/-- **The internal hom `SheafHom^dg_{𝒜'}(𝒩, -)`, extended to homogeneous maps** by
postcomposition. -/
noncomputable def sheafHomConcreteDGFunctor (N : DifferentialGradedBimodule.{u, a, z} A A') :
    ConcreteDGFunctor.{u, a, a, s, max u z s} A' A where
  functor := sheafHomFunctor N
  mapCochain c hc := sheafHomCochain (K := N.toRightModule) c ((isActionLinear_iff c).1 hc)
  isActionLinear_mapCochain c _ :=
    (isActionLinear_iff _).2 (cochainIsLinear_sheafHomCochain c _)
  mapCochain_add c c' _ _ _ := sheafHomCochain_add c c' _ _ _
  mapCochain_delta c _ _ := (sheafHomCochain_delta c _ _).symm
  mapCochain_comp c c' h _ _ _ := sheafHomCochain_comp c c' h _ _ _
  mapCochain_ofHom g := sheafHomCochain_ofHom g

/-- **The functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, extended to homogeneous maps.** -/
noncomputable def pushforwardSheafHomConcreteDGFunctor
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    ConcreteDGFunctor.{u, a, a', s, max u z s} A' B :=
  (sheafHomConcreteDGFunctor.{u, a, z, s} N).comp (pushforwardConcreteDGFunctor φ)

/-! ### Tag 0FTS -/

/-- **The functor `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`, `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`**, on homotopy
categories. -/
noncomputable def homotopyPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    HomotopyCategory.{u, a, s} A' ⥤ HomotopyCategory.{u, a', max u z s} B :=
  (pushforwardSheafHomConcreteDGFunctor.{u, a, a', z, s} φ N).homotopyFunctor

/-- The functor of Tag 0FTS factors `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` through the two quotient
functors. -/
theorem quotient_comp_homotopyPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    HomotopyCategory.quotient A' ⋙ homotopyPushforwardSheafHom.{u, a, a', z, s} φ N =
      (sheafHomFunctor N ⋙ pushforwardFunctor φ) ⋙ HomotopyCategory.quotient B :=
  (pushforwardSheafHomConcreteDGFunctor.{u, a, a', z, s} φ N).quotient_comp_homotopyFunctor

/-- The functor of Tag 0FTS commutes with the translations. -/
@[instance_reducible]
noncomputable instance homotopyPushforwardSheafHom_commShift
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    (homotopyPushforwardSheafHom.{u, a, a', z, s} φ N).CommShift ℤ :=
  (pushforwardSheafHomConcreteDGFunctor.{u, a, a', z, s} φ N).commShift

/-- The functor of Tag 0FTS is a triangulated functor. -/
instance homotopyPushforwardSheafHom_isTriangulated
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    (homotopyPushforwardSheafHom.{u, a, a', z, s} φ N).IsTriangulated :=
  (pushforwardSheafHomConcreteDGFunctor.{u, a, a', z, s} φ N).isTriangulated

/-- **The exact functor `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` along a continuous functor of sites.**
Let `f : 𝒟 ⥤ 𝒞` be a continuous functor with a structure map `σ : O_𝒟 ⟶ f_*O_𝒞`, let `𝒜` and
`𝒜'` be sheaves of differential graded algebras on `𝒞` and `ℬ` one on `𝒟`, let `φ : ℬ ⟶ f_*𝒜` be
a homomorphism and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule. Then the functor
`ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` induces a unique functor `K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`
through the two quotient functors, and it is exact. -/
theorem exists_isTriangulated_homotopyPushforwardSheafHom
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, a, z} A A') :
    ∃ (Φ : HomotopyCategory.{u, a, s} A' ⥤ HomotopyCategory.{u, a', max u z s} B)
      (_ : Φ.CommShift ℤ), Φ.IsTriangulated ∧
      HomotopyCategory.quotient A' ⋙ Φ =
        (sheafHomFunctor N ⋙ pushforwardFunctor φ) ⋙ HomotopyCategory.quotient B ∧
      ∀ Ψ : HomotopyCategory.{u, a, s} A' ⥤ HomotopyCategory.{u, a', max u z s} B,
        HomotopyCategory.quotient A' ⋙ Ψ =
          (sheafHomFunctor N ⋙ pushforwardFunctor φ) ⋙ HomotopyCategory.quotient B → Ψ = Φ :=
  ⟨homotopyPushforwardSheafHom φ N, inferInstance, inferInstance,
    quotient_comp_homotopyPushforwardSheafHom φ N,
    fun Ψ hΨ => HomotopyCategory.eq_descend _
      (pushforwardSheafHomConcreteDGFunctor.{u, a, a', z, s} φ N).preservesHomotopic Ψ hΨ⟩

/-- **The right derived extension of the functor of Tag 0FTS.** The functor
`K(Mod(𝒜', d)) ⥤ K(Mod(ℬ, d))`, `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)`, followed by the localization
`K(Mod(ℬ, d)) ⥤ D(ℬ, d)`, has a right derived extension `RT : D(𝒜', d) ⥤ D(ℬ, d)` along the
quasi-isomorphisms, as every right differential graded `𝒜'`-module has a quasi-isomorphism into
a graded injective K-injective one ([Stacks, Tag 0FT0]); this is the functor `RT` of
[Stacks, Tag 0FTT]. The sites, the algebras, the bimodule and the modules are taken in one
universe, where sheafification of abelian groups is available on both sites. -/
theorem exists_rightDerived_homotopyPushforwardSheafHom
    {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (φ : DifferentialGradedAlgebra.SemilinearHom f σ B A)
    (N : DifferentialGradedBimodule.{u, u, u} A A') :
    ∃ (RT : derivedCategory.{u, u, u} A' ⥤ derivedCategory.{u, u, u} B)
      (β : homotopyPushforwardSheafHom.{u, u, u, u, u} φ N ⋙ toDerivedCategory.{u, u, u} B ⟶
        toDerivedCategory.{u, u, u} A' ⋙ RT),
      RT.IsRightDerivedFunctor β (quasiIsomorphisms.{u, u, u} A') :=
  ⟨rightDerivedExtension.{u, u, u} _, rightDerivedExtensionUnit.{u, u, u} _,
    isRightDerivedFunctor_rightDerivedExtension.{u, u, u} _⟩

end DifferentialGradedModule

end SheafOfModules
