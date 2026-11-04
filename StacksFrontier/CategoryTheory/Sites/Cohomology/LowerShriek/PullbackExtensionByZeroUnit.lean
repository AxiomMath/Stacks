module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriekModules
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of the extension by zero of the structure sheaf, for an arbitrary structure map

Let `u : (C, J) ⥤ (D, K)` be a continuous functor of sites, `O` a sheaf of rings on `D`, `O'` a
sheaf of rings on `C` and `phi : O' ⟶ u_* O` a morphism of sheaves of rings whose module
pushforward has a left adjoint `g_!`. For an object `V` of `C`, morphisms out of
`g_!(j_{V!} O'_V)` are the sections over `u(V)`, so `g_!(j_{V!} O'_V) ≅ j_{u(V)!} O_{u(V)}` by
corepresentability. Both extensions by zero are the sheafified free modules
`Stacks.SheafOfModules.extensionByZeroUnit`.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.pullbackExtensionByZeroUnitCorepresentableBy`: the
  corepresentability of `Hom(g_!(j_{V!} O'_V), -)`.
* `Stacks.Cohomology.DerivedLowerShriek.pullbackExtensionByZeroUnitIso`: the isomorphism
  `g_!(j_{V!} O'_V) ≅ j_{u(V)!} O_{u(V)}`.

## Main results

* `extensionByZeroUnitHomEquiv_homEquiv_pullbackExtensionByZeroUnitIso_hom`:
  the adjoint transpose of that isomorphism, read through
  `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` on the source, is the universal section of
  `j_{u(V)!} O_{u(V)}` over `u(V)`.
* `Stacks.Cohomology.DerivedLowerShriek.homEquiv_pullbackExtensionByZeroUnitIso_hom`: the adjoint
  transpose of that isomorphism is the morphism attached to the universal section.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂ t

namespace Stacks.Cohomology.DerivedLowerShriek

section StructureMap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] (O : Sheaf K RingCat.{w}) (O' : Sheaf J RingCat.{w})
  (phi : O' ⟶ Stacks.SheafOfModules.inverseImageRing J K u O)
  [(SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).IsRightAdjoint]

/-- **Morphisms out of `g_! (j_{V!} O'_V)` are the sections over `u(V)`, for an arbitrary
structure morphism of sheaves of rings.** Here `g_!` is the left adjoint
`SheafOfModules.pullback phi` of the pushforward along `u` and `phi : O' ⟶ u_* O`, and
`j_{V!} O'_V` is the sheafified free module `Stacks.SheafOfModules.extensionByZeroUnit`. No
hypothesis is imposed on `phi`. -/
@[sga "2 I 1.7" "special case"]
def pullbackExtensionByZeroUnitCorepresentableBy (V : C) :
    (SheafOfModules.evaluation O (op (u.obj V)) ⋙
        forget (ModuleCat.{max u₁ v₁ u₂ v₂ w t}
          (O.obj.obj (op (u.obj V))))).CorepresentableBy
      ((SheafOfModules.pullback.{max u₁ v₁ u₂ v₂ w t} phi).obj
        (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, max u₂ v₂ t} O' V)) where
  homEquiv {F} :=
    ((SheafOfModules.pullbackPushforwardAdjunction.{max u₁ v₁ u₂ v₂ w t} phi).homEquiv _ F).trans
      (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, w, max u₂ v₂ t} O' V
        ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).obj F))
  homEquiv_comp {F G} g f :=
    (congrArg
        (fun a => Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, w, max u₂ v₂ t} O' V
          ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).obj G) a)
        ((SheafOfModules.pullbackPushforwardAdjunction.{max u₁ v₁ u₂ v₂ w t}
          phi).homEquiv_naturality_right f g)).trans
      (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, w, max u₂ v₂ t}
        O' V
        ((SheafOfModules.pullbackPushforwardAdjunction.{max u₁ v₁ u₂ v₂ w t} phi).homEquiv
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, max u₂ v₂ t} O' V) F f)
        ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).map g))

/-- **`g_! (j_{V!} O'_V) ≅ j_{u(V)!} O_{u(V)}` for an arbitrary structure morphism of sheaves
of rings.** For a continuous functor of sites `u : C ⥤ D`, a sheaf of rings `O` on `D`, a sheaf
of rings `O'` on `C`, *any* morphism `phi : O' ⟶ u_* O` whose module pushforward has a left
adjoint, and every object `V` of `C`,

`g_! (j_{V!} O'_V) ≅ j_{u(V)!} O_{u(V)}`,

where `g_! = SheafOfModules.pullback phi` and both extensions by zero are the sheafified free
modules `Stacks.SheafOfModules.extensionByZeroUnit`. -/
@[stacks 07AC "the second equality of the displayed chain, `g_! j_{U!} O_U = j_{u(U)!} \
O_{u(U)}`, on sheaves of modules, for an arbitrary structure morphism of sheaves of rings \
`O' ⟶ u_* O` and for the sheafified-free spelling of the extensions by zero. The first \
equality and the existence and adjointness of `Lg_!` are NOT covered: no unbounded total left \
derived functor of the module-level `g_!` is constructed in this library"]
def pullbackExtensionByZeroUnitIso (V : C) :
    (SheafOfModules.pullback.{max u₁ v₁ u₂ v₂ w t} phi).obj
        (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, max u₂ v₂ t} O' V) ≅
      Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V) :=
  (pullbackExtensionByZeroUnitCorepresentableBy.{w, v₁, u₁, v₂, u₂, t}
      J K u O O' phi V).uniqueUpToIso
    (Stacks.SheafOfModules.extensionByZeroUnitCorepresentableBy.{u₂, v₂, w, max u₁ v₁ t}
      O (u.obj V))

/-- The adjoint transpose of `pullbackExtensionByZeroUnitIso` under the adjunction `g_! ⊣ g^*`,
read through `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` on the source site, is the
universal section of `j_{u(V)!} O_{u(V)}` over `u(V)`: the section attached to the identity. -/
theorem extensionByZeroUnitHomEquiv_homEquiv_pullbackExtensionByZeroUnitIso_hom (V : C) :
    Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, w, max u₂ v₂ t} O' V
        ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).obj
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V)))
        ((SheafOfModules.pullbackPushforwardAdjunction.{max u₁ v₁ u₂ v₂ w t} phi).homEquiv
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, max u₂ v₂ t} O' V)
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V))
          (pullbackExtensionByZeroUnitIso.{w, v₁, u₁, v₂, u₂, t} J K u O O' phi V).hom) =
      Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V)
        (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V)) (𝟙 _) :=
  (pullbackExtensionByZeroUnitCorepresentableBy.{w, v₁, u₁, v₂, u₂, t}
    J K u O O' phi V).homEquiv.apply_symm_apply _

/-- The adjoint transpose of `pullbackExtensionByZeroUnitIso` under `g_! ⊣ g^*` is the morphism

`j_{V!} O'_V ⟶ g_* (j_{u(V)!} O_{u(V)})`

that `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` attaches to the universal section of
`j_{u(V)!} O_{u(V)}` over `u(V)`. -/
theorem homEquiv_pullbackExtensionByZeroUnitIso_hom (V : C) :
    (SheafOfModules.pullbackPushforwardAdjunction.{max u₁ v₁ u₂ v₂ w t} phi).homEquiv
        (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, max u₂ v₂ t} O' V)
        (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V))
        (pullbackExtensionByZeroUnitIso.{w, v₁, u₁, v₂, u₂, t} J K u O O' phi V).hom =
      (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, w, max u₂ v₂ t} O' V
          ((SheafOfModules.pushforward.{max u₁ v₁ u₂ v₂ w t} phi).obj
            (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t}
              O (u.obj V)))).symm
        (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₂, v₂, w, max u₁ v₁ t} O (u.obj V)
          (Stacks.SheafOfModules.extensionByZeroUnit.{u₂, v₂, w, max u₁ v₁ t}
            O (u.obj V)) (𝟙 _)) :=
  (Equiv.eq_symm_apply _).2
    (extensionByZeroUnitHomEquiv_homEquiv_pullbackExtensionByZeroUnitIso_hom.{w,
      v₁, u₁, v₂, u₂, t} J K u O O' phi V)

end StructureMap

end Stacks.Cohomology.DerivedLowerShriek

end
