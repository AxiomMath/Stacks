module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSliceEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness

/-!
# The inverse image along a 1-morphism commutes with the internal Hom

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}`, and let
`F`, `G` be sheaves of `𝒪_𝒴`-modules on the associated fppf site. Then

`f^* SheafHom_{𝒪_𝒴}(F, G) ≅ SheafHom_{𝒪_𝒳}(f^* F, f^* G)`.

This is the first step of the proof of **Stacks 0GQP**, which cites Modules on Sites,
Lemma 0GN2 for it and observes (Sheaves on Stacks, Remark 06TX) that flatness of `f` is not used:
the inverse image `f^* = f^{-1}` is restriction along `f`, and by Stacks 06W0 every slice functor
`𝒳/x ⥤ 𝒴/f(x)` is an equivalence, so the sections of both sides over `x` are the morphisms
`F|_{𝒴/f(x)} ⟶ G|_{𝒴/f(x)}`. Neither finite presentation of `F` nor flatness of `f` is needed;
the statement is the specialisation of
`Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso`.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullbackInternalHomSheafSmallIso`: the isomorphism for a
  1-morphism of categories fibred in groupoids, for the internal Hom at the module universe `u`
  of the schemes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesPullbackInternalHomIso`: the same along a
  1-morphism of algebraic stacks, for `AlgebraicGeometry.Stack.fppfModulesPullback`.

## References

* [Stacks Project, Tag 0GQP](https://stacks.math.columbia.edu/tag/0GQP)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
* [Stacks Project, Tag 06TX](https://stacks.math.columbia.edu/tag/06TX)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

include hp hq hf in
/-- The slice functors `𝒳/x ⥤ 𝒴/f(x)` of a 1-morphism of categories fibred in groupoids are
equivalences (Stacks 06W0). -/
theorem isEquivalence_overPost_of_comp_eq (x : 𝒳) : (Over.post (X := x) f).IsEquivalence := by
  subst p
  let r := q ⋙ Over.forget (B.obj hS)
  have : (Over.post (X := f.obj x) r).IsEquivalence := isEquivalence_overPost B S hS q hq (f.obj x)
  have : (Over.post (X := x) (f ⋙ r)).IsEquivalence := isEquivalence_overPost B S hS (f ⋙ q) hp x
  have : (Over.post (X := x) f ⋙ Over.post r).IsEquivalence := by
    rw [← Over.post_comp]
    infer_instance
  exact Functor.isEquivalence_of_comp_right (Over.post f) (Over.post r)

/-- The structure map of the inverse image of modules along a 1-morphism of categories fibred in
groupoids: the structure sheaf of the source is the restriction of the one of the target, and the
map is an `eqToHom`. -/
def modulePullbackStructureMap :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
      (B.topology.over (B.obj hS))).1
    ringStructureSheafCore B S hS p hp B.topology le_rfl ⟶
      (f.sheafPushforwardContinuous RingCat.{u} (associatedTopology B S hS p B.topology)
        (associatedTopology B S hS q B.topology)).obj
        (ringStructureSheafCore B S hS q hq B.topology le_rfl) :=
  ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf B.topology le_rfl)⟩

/-- The structure map of the inverse image of modules is invertible. -/
instance isIso_modulePullbackStructureMap :
    IsIso (modulePullbackStructureMap B S hS p q hp hq f hf) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).1
  have : IsIso ((sheafToPresheaf (associatedTopology B S hS p B.topology) RingCat.{u}).map
      (modulePullbackStructureMap B S hS p q hp hq f hf)) :=
    inferInstanceAs (IsIso
      (eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf B.topology le_rfl)))
  exact isIso_of_reflects_iso _
    (sheafToPresheaf (associatedTopology B S hS p B.topology) RingCat.{u})

variable [EssentiallySmall.{u} 𝒳] [EssentiallySmall.{u} 𝒴]

/-- The associated sites of an essentially small fibred category are essentially small. -/
local instance essentiallySmall_ringedSite_C {𝒵 : Type v} [Category.{w} 𝒵]
    [EssentiallySmall.{u} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS) (hr : r.IsFiberedInGroupoids)
    (τ : SiteKind) : EssentiallySmall.{u} (FibredSite.ringedSite B S hS r hr τ).C :=
  inferInstanceAs (EssentiallySmall.{u} 𝒵)

/-- **The inverse image along a 1-morphism of categories fibred in groupoids commutes with the
internal Hom** of `Mod(𝒪)` on the associated fppf sites, at the module universe `u` of the
schemes: `f^* SheafHom_{𝒪_𝒴}(F, G) ≅ SheafHom_{𝒪_𝒳}(f^* F, f^* G)` for arbitrary `F` and `G`.

This is the step of the proof of Stacks 0GQP the source attributes to Stacks 0GN2; here it needs
neither flatness of `f` nor finite presentation of `F`, because the slices of `f` are
equivalences (Stacks 06W0). -/
def modulePullbackInternalHomSheafSmallIso
    (F G : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS q hq .fppf)) :
    (modulePullback.{u, v, w, u, v, w} B S hS p q hp hq f hf B.topology le_rfl).obj
        (RingedSite.internalHomSheafSmall.{u} (FibredSite.ringedSite B S hS q hq .fppf) F G) ≅
      RingedSite.internalHomSheafSmall.{u} (FibredSite.ringedSite B S hS p hp .fppf)
        ((modulePullback.{u, v, w, u, v, w} B S hS p q hp hq f hf B.topology le_rfl).obj F)
        ((modulePullback.{u, v, w, u, v, w} B S hS p q hp hq f hf B.topology le_rfl).obj G) := by
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).1
  letI := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).2
  exact @Stacks.SheafOfModules.InternalHom.sliceEquivInternalHomSmallIso.{v, w, u, u}
    (FibredSite.ringedSite B S hS q hq .fppf) (FibredSite.ringedSite B S hS p hp .fppf) f
    ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
      (B.topology.over (B.obj hS))).1
    ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
      (B.topology.over (B.obj hS))).2
    (isEquivalence_overPost_of_comp_eq B S hS p q hp hq f hf)
    (modulePullbackStructureMap B S hS p q hp hq f hf)
    (isIso_modulePullbackStructureMap B S hS p q hp hq f hf) F G
    (essentiallySmall_ringedSite_C B S hS q hq .fppf)
    (essentiallySmall_ringedSite_C B S hS p hp .fppf)

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] AlgebraicGeometry.Stack.essentiallySmall_ringedSite_C

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image along a 1-morphism of algebraic stacks commutes with the internal Hom**
of `Mod(𝒪)`, at the module universe `u`: `f^* SheafHom_{𝒪_𝒴}(F, G) ≅ SheafHom_{𝒪_𝒳}(f^*F, f^*G)`
for arbitrary modules `F` and `G` on the fppf site of `𝒴`. -/
def fppfModulesPullbackInternalHomIso (F G : Stack.fppfModules B S hS 𝒴) :
    (fppfModulesPullback B S hS f).obj (RingedSite.internalHomSheafSmall.{u}
        (FibredSite.ringedSite B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf) F G) ≅
      RingedSite.internalHomSheafSmall.{u}
        (FibredSite.ringedSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)
        ((fppfModulesPullback B S hS f).obj F) ((fppfModulesPullback B S hS f).obj G) :=
  modulePullbackInternalHomSheafSmallIso B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom) F G

end AlgebraicGeometry.Stack.AlgebraicStacks

end
