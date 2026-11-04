module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcStack
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles
public import StacksFrontier.CategoryTheory.Sites.Descent.SubPseudofunctorStack
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData
public import StacksFrontier.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fpqc descent of finite locally free modules along one morphism

The pseudofunctor `AlgebraicGeometry.vectPseudofunctor` sends a scheme `X` to `Vect(X)`, the
category of finite locally free `𝒪_X`-modules, and a morphism to pullback.  This file proves that
it has effective descent along every surjective flat quasi-compact morphism, i.e. along every
one-element fpqc covering: Stacks Tag 023T for quasi-coherent modules, cut down to the finite
locally free ones by Stacks Tag 05B2.

## Main definitions

* `AlgebraicGeometry.finiteLocallyFreeProperty`: finite local freeness, as a property of the
  objects of the categories of `Stacks.Descent.qcohPseudofunctor` or of
  `AlgebraicGeometry.modulePullbackPseudofunctor`.
* `AlgebraicGeometry.vectPseudofunctor`: `X ↦ Vect(X)`.

## Main results

* `AlgebraicGeometry.isStackFor_vectPseudofunctor_singleton`: **effective descent of finite
  locally free modules along a surjective flat quasi-compact morphism.**

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Descent

universe u

namespace AlgebraicGeometry

/-- Finite local freeness, as a property of the objects of the categories of modules through which
`AlgebraicGeometry.modulePullbackPseudofunctor` takes its values. -/
def finiteLocallyFreeProperty : modulePullbackPseudofunctor.{u}.ObjectProperty where
  prop _X := fun M ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M

/-- Finite local freeness of modules is stable under pullback along morphisms of schemes. -/
instance : finiteLocallyFreeProperty.{u}.IsClosedUnderMapObj where
  map_obj {_ _ M} hM g := SheafOfModules.IsFiniteLocallyFree.pullback_scheme g.as.unop M hM

/-- **The pseudofunctor `X ↦ Vect(X)`** of finite locally free modules and pullbacks. -/
abbrev vectPseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  finiteLocallyFreeProperty.{u}.fullsubcategory

example (X : Scheme.{u}) : (vectPseudofunctor.obj (.mk (op X)) : Type _) = X.Vect := rfl

/-- Finite local freeness, as a property of the objects of the categories of quasi-coherent
modules. -/
def qcohFiniteLocallyFreeProperty : qcohPseudofunctor.{u}.ObjectProperty where
  prop _X := fun M ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M.obj

/-- Finite local freeness of quasi-coherent modules is stable under pullback along morphisms of
schemes. -/
instance : qcohFiniteLocallyFreeProperty.{u}.IsClosedUnderMapObj where
  map_obj {_ _ M} hM g := SheafOfModules.IsFiniteLocallyFree.pullback_scheme g.as.unop M.obj hM

/-- A quasi-coherent module isomorphic to a finite locally free one is finite locally free. -/
instance : qcohFiniteLocallyFreeProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms _X :=
    { of_iso := fun {_M _N} e hM ↦
        SheafOfModules.IsFiniteLocallyFree.of_iso ((ObjectProperty.ι _).mapIso e) (h := hM) }

/-- The comparison of `Vect(X)` with the finite locally free objects of the category of
quasi-coherent modules: an isomorphism of categories. -/
abbrev vectToQcohFiniteLocallyFree (X : Scheme.{u}) :
    (vectPseudofunctor.{u}.obj (.mk (op X)) : Type _) ⥤
      qcohFiniteLocallyFreeProperty.{u}.fullsubcategory.obj (.mk (op X)) :=
  ObjectProperty.lift _ (ObjectProperty.lift _ (ObjectProperty.ι _)
      (fun M ↦ by
        have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M.obj := M.property
        exact Stacks.Chow.isQuasicoherent_of_isFiniteLocallyFree M.obj))
    (fun M ↦ M.property)

/-- The comparison functor `AlgebraicGeometry.vectToQcohFiniteLocallyFree X` is an equivalence. -/
instance (X : Scheme.{u}) : (vectToQcohFiniteLocallyFree X).IsEquivalence where
  faithful := ⟨fun h ↦ InducedCategory.hom_ext (congrArg (fun φ ↦ φ.hom.hom) h)⟩
  full := ⟨fun φ ↦ ⟨ObjectProperty.homMk φ.hom.hom, rfl⟩⟩
  essSurj := ⟨fun M ↦ ⟨⟨M.obj.obj, M.property⟩, ⟨Iso.refl _⟩⟩⟩

/-- **`Vect` as a strong transformation into the finite locally free quasi-coherent modules**,
with identity components. -/
def vectToQcohFiniteLocallyFreeTrans :
    vectPseudofunctor.{u}.StrongTrans qcohFiniteLocallyFreeProperty.{u}.fullsubcategory :=
  Pseudofunctor.catStrongTransOfIsLocallyDiscrete _ _
    (fun a ↦ vectToQcohFiniteLocallyFree a.as.unop)
    (fun {_ _} _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))
    (fun _ _ ↦ rfl) (fun {a b c} f g M ↦ by
      refine InducedCategory.hom_ext (InducedCategory.hom_ext ?_)
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _ ≫ (modulePullbackPseudofunctor.map g).toFunctor.map (𝟙 _)
      rw [CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- **Effective descent of finite locally free modules along a surjective flat quasi-compact
morphism.**  Quasi-coherent modules have effective descent along it (Stacks Tag 023T,
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`), and finite local
freeness of a quasi-coherent module is detected after pullback along it (Stacks Tag 05B2,
`AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover`). -/
@[sga "1 VIII 1.12"]
theorem isStackFor_vectPseudofunctor_singleton {X Y : Scheme.{u}} (g : X ⟶ Y) [Flat g]
    [Surjective g] [QuasiCompact g] :
    vectPseudofunctor.{u}.IsStackFor (Presieve.singleton g) := by
  let 𝒰 : Y.Cover.{u + 1} Scheme.fpqcPrecoverage :=
    Precoverage.ZeroHypercover.singleton g (Scheme.Hom.singleton_mem_fpqcPrecoverage g)
  have h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.fpqcPrecoverage.{u} Y := 𝒰.mem₀
  have hqc : qcohPseudofunctor.{u}.IsStackFor (Presieve.ofArrows 𝒰.X 𝒰.f) :=
    isStackFor_of_forall_isEffective h𝒰
      (fun D ↦ QuasicoherentDescentData.isEffective_fpqcPrecoverage 𝒰.toPreZeroHypercover 𝒰.mem₀ D)
  have hflf : qcohFiniteLocallyFreeProperty.{u}.fullsubcategory.IsStackFor
      (Presieve.ofArrows 𝒰.X 𝒰.f) :=
    Stacks.Descent.isStackFor_fullsubcategory _ 𝒰.f
      (fun M hM ↦ isFiniteLocallyFree_of_pullback_fpqcCover (hqc := M.property) M.obj 𝒰 hM) hqc
  have hτ : ∀ a : LocallyDiscrete Scheme.{u}ᵒᵖ,
      (vectToQcohFiniteLocallyFreeTrans.app a).toFunctor.IsEquivalence :=
    fun a ↦ inferInstanceAs (vectToQcohFiniteLocallyFree a.as.unop).IsEquivalence
  have := (vectToQcohFiniteLocallyFreeTrans.isStackFor_iff_of_app_isEquivalence hτ
    (Presieve.ofArrows 𝒰.X 𝒰.f)).mpr hflf
  rwa [show Presieve.ofArrows 𝒰.X 𝒰.f = Presieve.singleton g from
    PreZeroHypercover.presieve₀_singleton g] at this

end AlgebraicGeometry

end
