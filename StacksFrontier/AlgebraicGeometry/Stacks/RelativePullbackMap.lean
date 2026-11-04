module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback

/-!
# Relative pullback maps

Let `Sh(𝒟) --f--> Sh(𝒞) --g--> Sh(ℬ)` be morphisms of topoi and let `h = g ∘ f`.  For a sheaf
`ℱ` on `𝒞` the *pullback map*

`f^{-1} : g_*ℱ ⟶ h_*f^{-1}ℱ`

is `g_*` applied to the unit `ℱ ⟶ f_*f^{-1}ℱ`, followed by the identification
`g_*f_*f^{-1}ℱ = h_*f^{-1}ℱ`.  Given moreover a sheaf `𝒢` on `𝒟` and a map `φ : f^{-1}ℱ ⟶ 𝒢`,
composing with `h_*φ` gives a map `g_*ℱ ⟶ h_*𝒢`.

Both maps are constructed for an adjunction `f^{-1} ⊣ f_*`, two direct images and an
identification of `f_* ⋙ g_*` with `h_*`, the first one as a natural transformation
`g_* ⟶ f^{-1} ⋙ h_*`.  The construction is then instantiated on `LQCoh^fbc`: for 1-morphisms
`pr : 𝒲 ⥤ 𝒴`, `a : 𝒴 ⥤ 𝒳` of categories fibred in groupoids and the composite `f : 𝒲 ⥤ 𝒳`, it
gives the comparison `a_*ℱ ⟶ f_*(pr^*ℱ)` between the direct images along the two legs.

## Main definitions

* `CategoryTheory.Adjunction.relativePullback`: **Stacks 06UM**, the pullback map
  `g_*ℱ ⟶ h_*f^{-1}ℱ` of a commutative triangle, as a natural transformation.
* `CategoryTheory.Adjunction.relativePullbackMapOfHom`: the map `g_*ℱ ⟶ h_*𝒢` attached to a
  morphism `f^{-1}ℱ ⟶ 𝒢`.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangePullback`: the inverse image
  `pr^* : LQCoh^fbc(𝒪_𝒴) ⥤ LQCoh^fbc(𝒪_𝒲)`, the inverse image of sheaves of modules of
  **Stacks 06WE** restricted to `LQCoh^fbc`.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRelativePullback`: the pullback
  map `a_*ℱ ⟶ f_*(pr^*ℱ)` between the direct images on `LQCoh^fbc` along the two legs of a
  factorization `𝒲 ⥤ 𝒴 ⥤ 𝒳`.

## Main results

* `CategoryTheory.Adjunction.relativePullback_app_id`: for the identity triangle the pullback
  map is the unit of the adjunction.
* `CategoryTheory.Adjunction.relativePullbackMapOfHom_naturality`: the map attached to
  `φ : f^{-1}ℱ ⟶ 𝒢` is natural in `ℱ`.

## Implementation notes

The commutativity of the triangle is the datum `c : f_* ⋙ g_* ≅ h_*` rather than an equality of
functors: for morphisms of topoi arising from morphisms of sites that identification is a
canonical isomorphism rather than a definitional equality.

The instantiation on `LQCoh^fbc` takes the three direct images and the identification
`pr_* ⋙ a_* ≅ f_*` as data (**Stacks 0771**).  The inverse image is constructed from
`AlgebraicGeometry.Stack.modulePullback`, with the hypothesis that it preserves `LQCoh^fbc`,
which is **Stacks 0771** part (3).

## References

* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Adjunction

variable {ℬ : Type u₁} [Category.{v₁} ℬ] {𝒞 : Type u₂} [Category.{v₂} 𝒞]
  {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  {finv : 𝒞 ⥤ 𝒟} {fstar : 𝒟 ⥤ 𝒞} (adjf : finv ⊣ fstar)
  (gstar : 𝒞 ⥤ ℬ) (hstar : 𝒟 ⥤ ℬ) (c : fstar ⋙ gstar ≅ hstar)

/-- **The relative pullback map of a commutative triangle.**  For an adjunction
`f^{-1} ⊣ f_*` and direct images `g_*`, `h_*` to a third category identified by
`c : f_* ⋙ g_* ≅ h_*`, the map

`g_*ℱ ⟶ h_*f^{-1}ℱ`

is `g_*` applied to the unit `ℱ ⟶ f_*f^{-1}ℱ`, followed by `c` at `f^{-1}ℱ`. -/
@[stacks 06UM "the relative pullback map g_*ℱ ⟶ h_*f^{-1}ℱ of a commutative triangle of \
morphisms of topoi, stated for an adjunction f^{-1} ⊣ f_*, two direct images and an \
isomorphism f_* ⋙ g_* ≅ h_* in place of the source's equality of functors"]
def relativePullback : gstar ⟶ finv ⋙ hstar where
  app F := gstar.map (adjf.unit.app F) ≫ c.hom.app (finv.obj F)
  naturality F F' φ := by
    have hu : φ ≫ adjf.unit.app F' = adjf.unit.app F ≫ fstar.map (finv.map φ) :=
      adjf.unit.naturality φ
    have hc := c.hom.naturality (finv.map φ)
    simp only [Functor.comp_obj, Functor.comp_map] at hc ⊢
    rw [← Category.assoc, ← gstar.map_comp, hu, gstar.map_comp, Category.assoc, hc]
    simp

/-- The relative pullback map at an object: `g_*` of the unit, followed by the identification
`g_*f_* ≅ h_*`. -/
@[simp]
theorem relativePullback_app (F : 𝒞) :
    (relativePullback adjf gstar hstar c).app F =
      gstar.map (adjf.unit.app F) ≫ c.hom.app (finv.obj F) :=
  rfl

/-- **The relative pullback map attached to a morphism `f^{-1}ℱ ⟶ 𝒢`.**  The pullback map
`g_*ℱ ⟶ h_*f^{-1}ℱ` followed by `h_*φ`. -/
@[stacks 06UM "the variant g_*ℱ ⟶ h_*𝒢 of the relative pullback map attached to a morphism \
f^{-1}ℱ ⟶ 𝒢"]
def relativePullbackMapOfHom (F : 𝒞) {G : 𝒟} (φ : finv.obj F ⟶ G) :
    gstar.obj F ⟶ hstar.obj G :=
  (relativePullback adjf gstar hstar c).app F ≫ hstar.map φ

/-- The relative pullback map attached to `φ : f^{-1}ℱ ⟶ 𝒢` is natural in `ℱ`: precomposing
with `g_*ψ` is the map attached to `f^{-1}ψ ≫ φ`. -/
theorem relativePullbackMapOfHom_naturality {F F' : 𝒞} (ψ : F ⟶ F') {G : 𝒟}
    (φ : finv.obj F' ⟶ G) :
    gstar.map ψ ≫ relativePullbackMapOfHom adjf gstar hstar c F' φ =
      relativePullbackMapOfHom adjf gstar hstar c F (finv.map ψ ≫ φ) := by
  rw [relativePullbackMapOfHom, relativePullbackMapOfHom, ← Category.assoc,
    (relativePullback adjf gstar hstar c).naturality ψ, Category.assoc]
  simp

/-- **For the identity triangle the relative pullback map is the unit of the adjunction.** -/
@[simp]
theorem relativePullback_app_id (F : 𝒞) :
    (relativePullback adjf (𝟭 𝒞) fstar fstar.rightUnitor).app F = adjf.unit.app F := by
  simp [relativePullback]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Stack

section Pullback

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴] {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (w : 𝒲 ⥤ BigFppfOver B S hS) (hw : w.IsFiberedInGroupoids)
  (y : 𝒴 ⥤ BigFppfOver B S hS) (hy : y.IsFiberedInGroupoids)
  (pr : 𝒲 ⥤ 𝒴) (hpr : pr ⋙ y = w)

/-- **The inverse image of modules in `LQCoh^fbc`.**  The inverse image of sheaves of modules on
the associated étale sites of **Stacks 06WE**, restricted to the locally quasi-coherent modules
with the flat base change property of **Stacks 07AQ**.  That it carries `LQCoh^fbc(𝒪_𝒴)` to
`LQCoh^fbc(𝒪_𝒲)` is **Stacks 0771** part (3), taken here as the hypothesis `hlq`. -/
def locallyQuasicoherentFlatBaseChangePullback
    (hlq : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS y hy,
      IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS w hw
        ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS w y hw hy pr hpr
          (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val) :
    locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS y hy ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS w hw :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun F : SheafOfModules.{u}
          (ringStructureSheafCore B S hS y hy (etaleTopology B)
            (etaleTopology_le_topology B)) =>
        IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS y hy F.val) ⋙
      modulePullback.{u, u + 1, u, u, u + 1, u} B S hS w y hw hy pr hpr
        (etaleTopology B) (etaleTopology_le_topology B))
    hlq

end Pullback

section RelativePullback

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (hE : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (x : 𝒳 ⥤ BigFppfOver B S hS) (hx : x.IsFiberedInGroupoids)
  (y : 𝒴 ⥤ BigFppfOver B S hS) (hy : y.IsFiberedInGroupoids)
  (w : 𝒲 ⥤ BigFppfOver B S hS) (hw : w.IsFiberedInGroupoids)

/-- **The relative pullback map between direct images on `LQCoh^fbc` along the two legs of a
factorization.**  Let `pr : 𝒲 ⥤ 𝒴` and let `a : 𝒴 ⥤ 𝒳`, `f : 𝒲 ⥤ 𝒳` be 1-morphisms of
categories fibred in groupoids with direct images `aStar`, `fStar` on `LQCoh^fbc` identified by
`cmp : pr_* ⋙ a_* ≅ f_*`.  The relative pullback map of **Stacks 06UM** at the adjunction
`pr^* ⊣ pr_*` is the natural transformation

`a_*ℱ ⟶ f_*(pr^*ℱ)`.

The inverse image `pr^*` is the one built from `AlgebraicGeometry.Stack.modulePullback`; the
direct images and their adjunction are the data of **Stacks 0771**. -/
def locallyQuasicoherentFlatBaseChangeRelativePullback
    (pr : 𝒲 ⥤ 𝒴) (hpr : pr ⋙ y = w)
    (hlq : ∀ M : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS y hy,
      IsLocallyQuasicoherentWithFlatBaseChange B E hE S hS w hw
        ((modulePullback.{u, u + 1, u, u, u + 1, u} B S hS w y hw hy pr hpr
          (etaleTopology B) (etaleTopology_le_topology B)).obj M.obj).val)
    (prStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS w hw ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS y hy)
    (adjPr : locallyQuasicoherentFlatBaseChangePullback B E hE S hS w hw y hy pr hpr hlq ⊣ prStar)
    (aStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS y hy ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS x hx)
    (fStar : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS w hw ⥤
      locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E hE S hS x hx)
    (cmp : prStar ⋙ aStar ≅ fStar) :
    aStar ⟶
      locallyQuasicoherentFlatBaseChangePullback B E hE S hS w hw y hy pr hpr hlq ⋙ fStar :=
  Adjunction.relativePullback adjPr aStar fStar cmp

end RelativePullback

end AlgebraicGeometry.Stack

end
