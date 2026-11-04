module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# The essential image of the associated-module functor

The associated-module functor of a morphism of ringed sites is a pullback, hence a left
adjoint, hence preserves coproducts and cokernels; and when the underlying functor of sites is
final it carries the free module on a type to the free module on that type.  Consequently its
essential image contains the free modules and is closed under those cokernels whose defining
morphism lies in the image of the functor on morphisms.

That is the first paragraph of the proof of Stacks Proposition 03DX: a module on the big site
presented as a cokernel
`⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0`
is `𝓕^a` for a quasi-coherent `𝓕` on the base, the quasi-coherent sheaf being the cokernel of
the morphism of free modules that presents the first map.  The source says "this is clear for
the direct sums" — that clause is `AlgebraicGeometry.BigFppfOver.essImage_associatedModule_free`
below — and then invokes the full faithfulness of `(-)^a`, Stacks 0GN7, to produce the morphism
of free modules downstairs.  Only that last step is assumed here, in the exact strength the
argument uses: `AlgebraicGeometry.BigFppfOver.IsFullOnFree`, fullness of `(-)^a` on *free*
modules alone.

## Main definitions

* `CategoryTheory.Functor.cokernelObjIsoOfIsColimitCokernelCofork`: a functor preserving a
  cokernel identifies the image of that cokernel with any other cokernel of the image morphism.
* `SheafOfModules.sectionsEquivPushforward`: the global sections of a sheaf of modules on the
  target of a final morphism of ringed sites are the global sections of its pushforward.
* `AlgebraicGeometry.BigFppfOver.IsFullOnFree`: fullness of the associated-module functor of the
  big fppf site of `S` on free modules, the one input of Stacks 03DX (1) that is not proved
  here.

## Main results

* `CategoryTheory.Functor.essImage_of_isColimit_cokernelCofork`: the essential image of a
  cokernel-preserving functor contains every cokernel of a morphism in the image of the functor.
* `SheafOfModules.essImage_pullback_free` and
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModule_free`: a free module on the target
  site is the associated module of the free module on the same type.
* `SheafOfModules.essImage_pullback_of_isColimit_cofan`: the essential image is closed under
  coproducts, with no restriction on the size of the index type.
* `SheafOfModules.nonempty_iso_pullbackObj_cokernel_free`: a cokernel of a morphism of free
  modules on the target site is the associated module of the cokernel of a morphism of free
  modules on the source site, provided the latter presents the former.
* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree`:
  the resulting module on `S` is quasi-coherent.  This is the local step of the essential
  surjectivity half of Stacks 03DX (1), for `τ = fppf`.

## Implementation notes

Nothing here is tagged.  The statement of Stacks 03DX (1) is an equivalence of categories, and
what is missing is its essential surjectivity half: the globalization of the local step proved
here over an fppf covering of `S` is the appeal to the effectivity of descent, Stacks 023T.  The
full faithfulness half, Stacks 0GN7, is **not** missing — it is
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`, at every `τ`, and the
Remark 03FH identification with the sections description that it is about is Stacks 070S (1),
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`; on the small sites the same
clause is `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` and
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`, with
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedSheafFunctor` for the sections-defined
functor.
`AlgebraicGeometry.BigFppfOver.IsFullOnFree` is 0GN7 restricted to free modules, and it is still
carried as a hypothesis of every statement below that needs it, this module being upstream of
the file that proves it.

The quantification of the index types is what forces the local step to be stated in terms of
free modules rather than of `SheafOfModules.HasGlobalPresentation`.  On the big fppf category of
`S` — objects in `Type (u + 1)`, morphisms, coefficients and sections in `Type u` — the
presentation universe `max u v r m` of `SheafOfModules.HasGlobalPresentation` is `u + 1`, so the
coproducts it provides are indexed by types in `Type (u + 1)` and live in
`SheafOfModules.{u + 1}`, whereas `SheafOfModules.free` on a site with coefficients in
`RingCat.{u}` is indexed by `Type u`.  A presentation in the sense of
`SheafOfModules.HasGlobalPresentation` therefore cannot be matched against the free modules that
the associated-module functor produces, and the two notions meet only after a universe
restriction that is not available at this pin.

The morphism `α` below is a morphism of free modules on the big site and the hypothesis `hβ`
says that `β` presents it *after* transport along `SheafOfModules.pullbackObjFreeIso`; stating it
that way keeps `α` where the source puts it, on the big site, while `β` is where the cokernel is
formed.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

/-- A functor preserving the cokernel of `f` identifies the image of that cokernel with any
object exhibited as a cokernel of the image of `f`. -/
public noncomputable def cokernelObjIsoOfIsColimitCokernelCofork
    {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [HasZeroMorphisms B]
    (Φ : A ⥤ B) [Φ.PreservesZeroMorphisms]
    {X Y : A} (f : X ⟶ Y) [HasCokernel f] [PreservesColimit (parallelPair f 0) Φ]
    {G : B} {π : Φ.obj Y ⟶ G} (hπ : Φ.map f ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    Φ.obj (cokernel f) ≅ G :=
  IsColimit.coconePointUniqueUpToIso
    (isColimitOfHasCokernelOfPreservesColimit Φ f) hc

/-- The essential image of a functor preserving the cokernel of `f` contains every object
exhibited as a cokernel of the image of `f`. -/
public theorem essImage_of_isColimit_cokernelCofork
    {A : Type u₁} [Category.{v₁} A] [HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [HasZeroMorphisms B]
    (Φ : A ⥤ B) [Φ.PreservesZeroMorphisms]
    {X Y : A} (f : X ⟶ Y) [HasCokernel f] [PreservesColimit (parallelPair f 0) Φ]
    {G : B} {π : Φ.obj Y ⟶ G} (hπ : Φ.map f ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    Φ.essImage G :=
  ⟨cokernel f, ⟨Φ.cokernelObjIsoOfIsColimitCokernelCofork f hπ hc⟩⟩

end CategoryTheory.Functor

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final]

/-- **The global sections of a pushforward.**  Along a morphism of ringed sites whose underlying
functor of sites is final, the global sections of a sheaf of modules and of its pushforward
agree. -/
public noncomputable def sectionsEquivPushforward (M : SheafOfModules.{u} R) :
    M.sections ≃ ((pushforward.{u} φ).obj M).sections :=
  Equiv.ofBijective _ (bijective_pushforwardSections φ M)

/-- A free sheaf of modules on the target site is the pullback of the free sheaf of modules on
the same type: the essential image of the pullback contains the free modules. -/
public theorem essImage_pullback_free (I : Type u) :
    (pullback.{u} φ).essImage (free I) :=
  ⟨free I, ⟨pullbackObjFreeIso φ I⟩⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final] in
/-- A coproduct of pullbacks is the pullback of the coproduct: the pullback is a left adjoint,
so it preserves coproducts, and the index type is unrestricted. -/
public theorem nonempty_iso_pullbackObj_sigma {I : Type w} (N : I → SheafOfModules.{u} S)
    [HasCoproduct N] {G : SheafOfModules.{u} R}
    (ι : ∀ i, (pullback.{u} φ).obj (N i) ⟶ G) (hc : IsColimit (Cofan.mk G ι)) :
    Nonempty ((pullback.{u} φ).obj (∐ N) ≅ G) := by
  let _ : PreservesColimitsOfSize.{w, w} (pullback.{u} φ) :=
    (pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits
  have h : IsColimit (Cofan.mk ((pullback.{u} φ).obj (∐ N))
      (fun i => (pullback.{u} φ).map (Sigma.ι N i))) :=
    (Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk (∐ N) (Sigma.ι N))).toFun
      (isColimitOfPreserves _ (coproductIsCoproduct N))
  exact ⟨IsColimit.coconePointUniqueUpToIso h hc⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final] in
/-- The essential image of the pullback is closed under coproducts of arbitrary size. -/
public theorem essImage_pullback_of_isColimit_cofan {I : Type w} (N : I → SheafOfModules.{u} S)
    [HasCoproduct N] {G : SheafOfModules.{u} R}
    (ι : ∀ i, (pullback.{u} φ).obj (N i) ⟶ G) (hc : IsColimit (Cofan.mk G ι)) :
    (pullback.{u} φ).essImage G :=
  ⟨∐ N, nonempty_iso_pullbackObj_sigma φ N ι hc⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final] in
/-- A cokernel of the pullback of `β` is the pullback of the cokernel of `β`: the pullback is a
left adjoint, so it preserves cokernels. -/
public theorem nonempty_iso_pullbackObj_cokernel
    {N₂ N₁ : SheafOfModules.{u} S} (β : N₂ ⟶ N₁) [HasCokernel β]
    {G : SheafOfModules.{u} R} {π : (pullback.{u} φ).obj N₁ ⟶ G}
    (hπ : (pullback.{u} φ).map β ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    Nonempty ((pullback.{u} φ).obj (cokernel β) ≅ G) :=
  let : PreservesColimitsOfSize.{0, 0} (pullback.{u} φ) :=
    (pullbackPushforwardAdjunction.{u} φ).leftAdjoint_preservesColimits
  ⟨Functor.cokernelObjIsoOfIsColimitCokernelCofork _ β hπ hc⟩

/-- **A cokernel of a morphism of free modules is a pullback.**  Let `α` be a morphism of free
sheaves of modules on the target site and let `β` be a morphism of free sheaves of modules on
the source site whose pullback is `α`, read through the identification of the pullback of a free
module with a free module.  Then every cokernel of `α` is the pullback of the cokernel of `β`. -/
public theorem nonempty_iso_pullbackObj_cokernel_free
    {I₁ I₂ : Type u} (α : free (R := R) I₂ ⟶ free I₁)
    (β : free (R := S) I₂ ⟶ free I₁) [HasCokernel β]
    (hβ : (pullback.{u} φ).map β =
      (pullbackObjFreeIso φ I₂).hom ≫ α ≫ (pullbackObjFreeIso φ I₁).inv)
    {G : SheafOfModules.{u} R} {π : free (R := R) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    Nonempty ((pullback.{u} φ).obj (cokernel β) ≅ G) := by
  set e₁ := pullbackObjFreeIso φ I₁
  set e₂ := pullbackObjFreeIso φ I₂
  have hπ' : (pullback.{u} φ).map β ≫ (e₁.hom ≫ π) = 0 := by
    rw [hβ]
    simp [hπ]
  refine nonempty_iso_pullbackObj_cokernel φ β hπ' ?_
  refine Cofork.isColimitOfIsos _ hc _ e₂.symm e₁.symm (Iso.refl _) ?_ ?_ ?_
  · simp [hβ]
  · simp
  · simp

/-- The essential image of the pullback contains every cokernel of a morphism of free modules
that is itself the pullback of a morphism of free modules. -/
public theorem essImage_pullback_of_isColimit_cokernelCofork_free
    {I₁ I₂ : Type u} (α : free (R := R) I₂ ⟶ free I₁)
    (β : free (R := S) I₂ ⟶ free I₁) [HasCokernel β]
    (hβ : (pullback.{u} φ).map β =
      (pullbackObjFreeIso φ I₂).hom ≫ α ≫ (pullbackObjFreeIso φ I₁).inv)
    {G : SheafOfModules.{u} R} {π : free (R := R) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    (pullback.{u} φ).essImage G :=
  ⟨cokernel β, nonempty_iso_pullbackObj_cokernel_free φ α β hβ hπ hc⟩

end SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global sections of a restriction.**  The global sections of a sheaf of modules on the
big fppf site of `S` are the global sections of its restriction to the small Zariski site of
`S`: the inclusion of the small Zariski site is a final functor. -/
public noncomputable def sectionsEquivRestrictModule
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    G.sections ≃ ((restrictModule B S hS).obj G).sections :=
  SheafOfModules.sectionsEquivPushforward (structureMap B S hS) G

/-- **Stacks 03DX, the direct sums.**  A free sheaf of modules on the big fppf site of `S` is the
associated module of the free `𝒪_S`-module on the same type. -/
public theorem essImage_associatedModule_free (I : Type u) :
    (associatedModule B S hS).essImage (SheafOfModules.free I) :=
  SheafOfModules.essImage_pullback_free (structureMap B S hS) I

/-- **Fullness of `𝓕 ↦ 𝓕^a` on free modules.**  Every morphism between the associated modules of
two free `𝒪_S`-modules is the associated morphism of a morphism of free `𝒪_S`-modules.

This is the restriction to free modules of the full faithfulness of `𝓕 ↦ 𝓕^a`, Stacks 0GN7, and
it is the one step of the essential surjectivity argument of Stacks 03DX (1) that is not proved
here: Stacks deduces 0GN7 from Remark 03FH, which identifies `𝓕^a` with a pullback of ringed
sites, and that remark rests on Stacks 070S (1). -/
public def IsFullOnFree : Prop :=
  ∀ (I₁ I₂ : Type u)
    (α : (associatedModule B S hS).obj (SheafOfModules.free (R := S.ringCatSheaf) I₂) ⟶
      (associatedModule B S hS).obj (SheafOfModules.free (R := S.ringCatSheaf) I₁)),
    ∃ β : (SheafOfModules.free (R := S.ringCatSheaf) I₂) ⟶ SheafOfModules.free I₁,
      (associatedModule B S hS).map β = α

/-- **Stacks 03DX (1), essential surjectivity, local step, for `τ = fppf`.**  A sheaf of modules
on the big fppf site of `S` presented as a cokernel
`⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0`
is the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`, namely of the cokernel of
the morphism of free `𝒪_S`-modules that presents the first map.

The hypothesis `hfull` is `AlgebraicGeometry.BigFppfOver.IsFullOnFree`: it is what produces that
morphism downstairs, and it is the restriction to free modules of Stacks 0GN7.  Everything else
is the left adjointness of `𝓕 ↦ 𝓕^a` together with the identification of the associated module
of a free module with a free module. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_cokernelFree
    (hfull : IsFullOnFree B S hS) {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) := by
  obtain ⟨β, hβ⟩ := hfull I₁ I₂
    ((SheafOfModules.pullbackObjFreeIso (structureMap B S hS) I₂).hom ≫ α ≫
      (SheafOfModules.pullbackObjFreeIso (structureMap B S hS) I₁).inv)
  exact ⟨cokernel β, Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (X := S) (M := SheafOfModules.free I₂) (N := SheafOfModules.free I₁) β,
    SheafOfModules.nonempty_iso_pullbackObj_cokernel_free (structureMap B S hS) α β hβ hπ hc⟩

/-- **Stacks 03DX (1), essential surjectivity, local step, for `τ = fppf`**, in the form of a
membership in the essential image of `𝓕 ↦ 𝓕^a`. -/
public theorem essImage_associatedModule_of_cokernelFree
    (hfull : IsFullOnFree B S hS) {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    (associatedModule B S hS).essImage G := by
  obtain ⟨G', _, h⟩ :=
    exists_isQuasicoherent_iso_associatedModule_of_cokernelFree B S hS hfull α hπ hc
  exact ⟨G', h⟩

end AlgebraicGeometry.BigFppfOver

end
