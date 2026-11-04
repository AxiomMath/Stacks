module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules

/-!
# Tensor products of modules on the sites of a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids whose total category is
essentially small.  Each of its five associated topologies makes `𝒳` a ringed site with the
structure sheaf of Stacks 06TV.  On each of them the tensor product of two sheaves of modules,
the sheafification `Stacks.SheafOfModules.Tensor.sheafTensor` of the objectwise tensor product of
the underlying presheaves, has the bilinear universal property: the pure-tensor map is bilinear
on sections, natural in both factors, compatible with restriction, and every bilinear map of
sections into a sheaf of modules factors uniquely through it.

This is the existence half of Stacks 06WN(2); the quasi-coherence of the tensor product of two
quasi-coherent modules, and the agreement of the tensor products computed for the different
topologies, are not stated here.

## Main definitions

* `PresheafOfModules.tensorSheafBilinear` is the pure-tensor map of two sheaves of modules on an
  arbitrary site, as a `Stacks.BilinearMap`.
* `AlgebraicGeometry.FibredSite.tensorTmul` is the pure-tensor map on sections on an associated
  site of the fibred category, and `AlgebraicGeometry.FibredSite.tensorTmulBilinear` is that map
  as a `Stacks.BilinearMap`.
* `AlgebraicGeometry.FibredSite.siteRestriction` reads a sheaf of modules for the fppf topology as
  a sheaf of modules for a coarser associated topology.
* `AlgebraicGeometry.FibredSite.tensorSiteComparison` is the canonical morphism from the tensor
  product computed for a coarser associated topology to the one computed for the fppf topology.

## Main results

* `PresheafOfModules.tensorSheaf_existsUnique_hom`: on an arbitrary site, every bilinear map of
  sections of two sheaves of modules into a third factors through the pure-tensor map by a
  unique morphism of sheaves of modules.
* `PresheafOfModules.tensorSheafUnit_tmul_map`: naturality of the pure-tensor map in both
  factors.
* `AlgebraicGeometry.FibredSite.tensorModules_existsUnique_hom`,
  `AlgebraicGeometry.FibredSite.tensorTmul_map` and
  `AlgebraicGeometry.FibredSite.tensorTmul_restrict`: the universal property, naturality and
  compatibility with restriction on each of the five sites associated with the fibred category.
* `AlgebraicGeometry.FibredSite.tensorSiteComparison_unique`: the comparison morphism is the only
  morphism carrying pure tensors to pure tensors.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe v u w a

namespace PresheafOfModules

/-! ### The universal property of the tensor product of two sheaves of modules

On an arbitrary site, the tensor product of two sheaves of modules is the sheafification of the
objectwise tensor product of the underlying presheaves, and a morphism out of it is the same
thing as a bilinear map on sections. -/

section TensorUniversal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

variable (F G : SheafOfModules.{a} (toRingCat J Osharp)) in
/-- The pure-tensor map of two sheaves of modules, as a bilinear map of the underlying
presheaves of modules: on sections it sends `x` and `y` to the image of `x ⊗ y` under the
morphism exhibiting the tensor product as a sheafification. -/
noncomputable def tensorSheafBilinear :
    Stacks.BilinearMap F.val G.val
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} Osharp).obj F).obj G).val :=
  toBilinear (tensorSheafUnit F G)

variable {F G H : SheafOfModules.{a} (toRingCat J Osharp)}

/-- The bilinear map `tensorSheafBilinear F G` sends sections `x` and `y` to the image of
`x ⊗ y` under `tensorSheafUnit F G`. -/
@[simp]
theorem tensorSheafBilinear_app (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (tensorSheafBilinear F G).app U x y = (tensorSheafUnit F G).app U (x ⊗ₜ y) :=
  rfl

/-- **The bilinear universal property of the tensor product of two sheaves of modules.**  Every
bilinear map of sections into a sheaf of modules factors through the pure-tensor map by a unique
morphism of sheaves of modules. -/
theorem tensorSheaf_existsUnique_hom (b : Stacks.BilinearMap F.val G.val H.val) :
    ∃! f : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} Osharp).obj F).obj G ⟶ H,
      ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
        f.val.app U ((tensorSheafUnit F G).app U (x ⊗ₜ y)) = b.app U x y := by
  have key := fun U x y ↦
    (tensorSheafDesc_unit (ofBilinear (O := Osharp.obj) b) U x y).trans (ofBilinear_tmul b U x y)
  exact ⟨_, key, fun g hg ↦ tensorSheaf_hom_ext fun U x y ↦ (hg U x y).trans (key U x y).symm⟩

/-- Naturality of the pure-tensor map in both factors. -/
theorem tensorSheafUnit_tmul_map
    {F' : SheafOfModules.{a} (toRingCat J Osharp)}
    {G' : SheafOfModules.{a} (toRingCat J Osharp)} (φ : F ⟶ F') (ψ : G ⟶ G') (U : Cᵒᵖ)
    (x : F.val.obj U) (y : G.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} Osharp).map φ).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} Osharp).obj _).map ψ)).val.app U
        ((tensorSheafUnit F G).app U (x ⊗ₜ y)) =
      (tensorSheafUnit F' G').app U (φ.val.app U x ⊗ₜ ψ.val.app U y) :=
  (congrArg (fun tensorMap => tensorMap.val.app U ((tensorSheafUnit F G).app U (x ⊗ₜ y)))
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, v, w, a, a} Osharp φ ψ)).trans
      ((unit_naturality_apply (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
        (tensorHom φ.val ψ.val) U (x ⊗ₜ y)).trans
        (congrArg (fun tensor => (tensorSheafUnit F' G').app U tensor)
          (tensorHom_tmul φ.val ψ.val U x y)))

end TensorUniversal

end PresheafOfModules

namespace AlgebraicGeometry.FibredSite

open PresheafOfModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS)

attribute [local instance] hasWeakSheafify_associatedTopology
  wEqualsLocallyBijective_associatedTopology

variable (hp : p.IsFiberedInGroupoids)

/-- The coefficient sheaf of rings for modules on an associated site of the fibred category is
the underlying sheaf of rings of its commutative structure sheaf. -/
public theorem toRingCat_structureSheaf (τ : SiteKind) :
    toRingCat (BigFppfOver.associatedTopology B S hS p τ) (structureSheaf B S hS p hp τ) =
      ringStructureSheafCore B S hS p hp τ :=
  rfl

variable (τ : SiteKind)

/-- The pure-tensor map on sections: the image of `x ⊗ y` under the morphism exhibiting the
tensor product sheaf as the sheafification of the objectwise tensor product. -/
public noncomputable def tensorTmul
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) (X : 𝒳ᵒᵖ)
    (x : F.val.obj X) (y : G.val.obj X) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS p hp τ)).obj F).obj G).val.obj X :=
  (tensorSheafUnit (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ) F G).app X (x ⊗ₜ y)

variable (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) in
/-- The pure-tensor map of two sheaves of modules on an associated site, as a bilinear map of
presheaves of modules on `𝒳`. -/
public noncomputable def tensorTmulBilinear :
    Stacks.BilinearMap F.val G.val
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS p hp τ)).obj F).obj G).val :=
  tensorSheafBilinear (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ) F G

variable {F G H : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)}

/-- The bilinear map `tensorTmulBilinear` sends sections `x` and `y` to `tensorTmul x y`. -/
@[simp]
public theorem tensorTmulBilinear_app (X : 𝒳ᵒᵖ) (x : F.val.obj X) (y : G.val.obj X) :
    (tensorTmulBilinear B S hS p hp τ F G).app X x y = tensorTmul B S hS p hp τ F G X x y :=
  rfl

/-- The pure-tensor map is compatible with the restriction maps of the three sheaves. -/
public theorem tensorTmul_restrict {X Y : 𝒳ᵒᵖ} (f : X ⟶ Y) (x : F.val.obj X)
    (y : G.val.obj X) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS p hp τ)).obj F).obj G).val.map
      f (tensorTmul B S hS p hp τ F G X x y) =
      tensorTmul B S hS p hp τ F G Y (F.val.map f x) (G.val.map f y) :=
  (tensorTmulBilinear B S hS p hp τ F G).naturality f x y

/-- **The bilinear universal property of the tensor product.**  On each of the five sites
associated with the fibred category, every bilinear map of sections of two sheaves of modules
into a third factors through the pure-tensor map by a unique morphism of sheaves of modules. -/
public theorem tensorModules_existsUnique_hom (b : Stacks.BilinearMap F.val G.val H.val) :
    ∃! f : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS p hp τ)).obj F).obj G ⟶ H,
      ∀ (X : 𝒳ᵒᵖ) (x : F.val.obj X) (y : G.val.obj X),
        f.val.app X (tensorTmul B S hS p hp τ F G X x y) = b.app X x y :=
  tensorSheaf_existsUnique_hom (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ) b

/-- Naturality of the pure-tensor map in both factors. -/
public theorem tensorTmul_map
    {F' G' : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)}
    (φ : F ⟶ F') (ψ : G ⟶ G') (X : 𝒳ᵒᵖ) (x : F.val.obj X) (y : G.val.obj X) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS p hp τ)).map φ).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS p hp τ)).obj _).map ψ)).val.app X
        (tensorTmul B S hS p hp τ F G X x y) =
      tensorTmul B S hS p hp τ F' G' X (φ.val.app X x) (ψ.val.app X y) :=
  tensorSheafUnit_tmul_map (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ) φ ψ X x y

/-! ### Comparing the tensor products computed for two of the topologies

All five associated topologies have the same underlying category and the same structure
presheaf, so a sheaf for the fppf topology is a sheaf for each coarser one and its presheaf of
sections does not change.  Both tensor products are therefore sheafifications of **one**
presheaf, for two different topologies, and the coarser one maps canonically to the finer one.
Stacks 06WN(2) is the assertion that this canonical map is an isomorphism when both factors are
quasi-coherent. -/

/-- A sheaf of modules for the inherited fppf topology, read as a sheaf of modules for a coarser
inherited topology.  Neither the underlying presheaf of modules nor the maps between them
change: the coefficient sheaf of rings has the same presheaf for all five topologies, and a
sheaf for the inherited fppf topology is a sheaf for each coarser inherited topology.  This is
`AlgebraicGeometry.FibredSite.toSiteModules` without the quasi-coherence hypothesis. -/
public def siteRestriction (τ : SiteKind) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ) where
  obj M := ⟨M.val, M.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS p τ)⟩
  map f := ⟨f.val⟩

/-- The canonical comparison from the tensor product of two module sheaves computed for a
coarser associated topology to the tensor product computed for the fppf topology: the unique
morphism of module sheaves on `𝒳_τ` carrying the `τ`-pure tensor of two sections to their
fppf-pure tensor.  Stacks 06WN(2) asserts that this morphism is an isomorphism when both factors
are quasi-coherent. -/
public noncomputable def tensorSiteComparison
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS p hp τ)).obj ((siteRestriction B S hS p hp τ).obj F)).obj
        ((siteRestriction B S hS p hp τ).obj G) ⟶
      (siteRestriction B S hS p hp τ).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS p hp .fppf)).obj F).obj G) :=
  tensorSheafDesc (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ)
    (tensorSheafUnit (J := BigFppfOver.associatedTopology B S hS p .fppf)
      (Osharp := structureSheaf B S hS p hp .fppf) F G)

/-- The comparison morphism carries the pure tensor computed for the coarser topology to the
pure tensor computed for the fppf topology. -/
public theorem tensorSiteComparison_tmul
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) (X : 𝒳ᵒᵖ)
    (x : F.val.obj X) (y : G.val.obj X) :
    (tensorSiteComparison B S hS p hp τ F G).val.app X
        (tensorTmul B S hS p hp τ ((siteRestriction B S hS p hp τ).obj F)
          ((siteRestriction B S hS p hp τ).obj G) X x y) =
      tensorTmul B S hS p hp .fppf F G X x y :=
  tensorSheafDesc_unit (J := BigFppfOver.associatedTopology B S hS p τ)
    (Osharp := structureSheaf B S hS p hp τ)
    (F := (siteRestriction B S hS p hp τ).obj F)
    (G := (siteRestriction B S hS p hp τ).obj G)
    (Q := (siteRestriction B S hS p hp τ).obj (((Stacks.SheafOfModules.Tensor.sheafTensor
      (structureSheaf B S hS p hp .fppf)).obj F).obj G))
    _ X x y

/-- The comparison morphism is the only morphism of module sheaves on `𝒳_τ` that carries pure
tensors to pure tensors. -/
public theorem tensorSiteComparison_unique
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (f : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS p hp τ)).obj ((siteRestriction B S hS p hp τ).obj F)).obj
        ((siteRestriction B S hS p hp τ).obj G) ⟶
      (siteRestriction B S hS p hp τ).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS p hp .fppf)).obj F).obj G))
    (hf : ∀ (X : 𝒳ᵒᵖ) (x : F.val.obj X) (y : G.val.obj X),
      f.val.app X (tensorTmul B S hS p hp τ ((siteRestriction B S hS p hp τ).obj F)
          ((siteRestriction B S hS p hp τ).obj G) X x y) =
        tensorTmul B S hS p hp .fppf F G X x y) :
    f = tensorSiteComparison B S hS p hp τ F G :=
  (tensorModules_existsUnique_hom B S hS p hp τ
      (F := (siteRestriction B S hS p hp τ).obj F)
      (G := (siteRestriction B S hS p hp τ).obj G)
      (H := (siteRestriction B S hS p hp τ).obj (((Stacks.SheafOfModules.Tensor.sheafTensor
        (structureSheaf B S hS p hp .fppf)).obj F).obj G))
      (tensorTmulBilinear B S hS p hp .fppf F G)).unique hf
    fun X x y ↦ tensorSiteComparison_tmul B S hS p hp τ F G X x y

end AlgebraicGeometry.FibredSite

end
