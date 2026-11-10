module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.PushforwardTerminalSectionsComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ring map on global sections is functorial

A morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` induces a ring map
`Γ(D, O_D) ⟶ Γ(C, O_C)` on global sections,
`Stacks.Cohomology.SiteModules.globalSectionsRingHom`. This ring map is functorial: for
`φ : X ⟶ Y`, `ψ : Y ⟶ Z` and a morphism `χ : X ⟶ Z` presented as their composite by a natural
transformation `τ : φ_* ⋙ ψ_* ⟶ χ_*` of direct images of `𝒪`-modules, together with its
underlying natural transformation `τ₀` of direct images of sheaves of sets,

`globalSectionsRingHom χ = (globalSectionsRingHom φ) ∘ (globalSectionsRingHom ψ)`.

## Main results

* `CategoryTheory.Functor.CorepresentableBy.homEquiv_uniqueUpToIso_hom_comp`: the comparison of
  two objects corepresenting the same functor transports one corepresentation to the other.
* `Stacks.Cohomology.SiteModules.unitTerminalHomEquiv_pushforwardUnitHomEquiv`: the adjunction
  bijection `Hom(1_{O_D}, f_*N) ≃ Hom(1_{O_C}, N)` is, after reading both sides as global
  sections of sheaves of sets, the comparison `MorphismOfTopoi.pushforwardTerminalHomEquiv`.
* `Stacks.Cohomology.SiteModules.pushforwardUnitHomEquiv_natTrans`: that bijection is
  compatible with `τ`.
* `Stacks.Cohomology.SiteModules.globalSectionsRingHom_natTrans`: the ring map on global
  sections is functorial.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos)
open Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe w w' w'' v u v' u' v'' u''

namespace CategoryTheory.Functor.CorepresentableBy

/-- For `e` corepresenting `F` by `A` and `e'` by `A'`, the isomorphism `A ≅ A'` of
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` carries `e'` to `e`: precomposing a
morphism out of `A'` with it and reading the result through `e` is reading the morphism through
`e'`. -/
@[ega "0 8.1.11" "partial"]
theorem homEquiv_uniqueUpToIso_hom_comp {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    {A A' : C} (e : F.CorepresentableBy A) (e' : F.CorepresentableBy A')
    {Z : C} (h : A' ⟶ Z) :
    e.homEquiv ((e.uniqueUpToIso e').hom ≫ h) = e'.homEquiv h := by
  have h0 : e.homEquiv (e.uniqueUpToIso e').hom = e'.homEquiv (𝟙 A') :=
    e.homEquiv.apply_symm_apply _
  rw [e.homEquiv_comp h, h0, ← e'.homEquiv_comp h (𝟙 A'), Category.id_comp]

end CategoryTheory.Functor.CorepresentableBy

namespace Stacks.Cohomology.SiteModules

section Geometric

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- The identification `f^*O_D ≅ O_C` at the structure sheaf transports the corepresentation of
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitCorepresentableBy` to the tautological
one: precomposing a morphism out of `f^*(1_{O_D})` with it is reading that morphism as a global
section through the adjunction `f^* ⊣ f_*`. -/
theorem pullbackModulesObjUnitIso_hom_comp (N : SheafOfModules.{w} (ringSheaf X.O))
    (h : (f.pullbackModules).obj (SheafOfModules.unit (ringSheaf Y.O)) ⟶ N) :
    (pullbackModulesObjUnitIso f).hom ≫ h =
      (unitTerminalHomEquiv (ringSheaf X.O) N).symm
        (pushforwardModulesUnitHomEquiv f N
          ((pullbackAdjPushforwardModules f).homEquiv _ N h)) :=
  (Functor.CorepresentableBy.coyoneda
    (Opposite.op (SheafOfModules.unit (ringSheaf X.O)))).homEquiv_uniqueUpToIso_hom_comp
      (pullbackModulesObjUnitCorepresentableBy f) h

/-- Reading morphisms out of the free module of rank one as global sections of the underlying
sheaf of sets, the bijection `Stacks.Cohomology.SiteModules.pushforwardUnitHomEquiv` becomes
`MorphismOfTopoi.pushforwardTerminalHomEquiv`. -/
theorem unitTerminalHomEquiv_pushforwardUnitHomEquiv
    (N : SheafOfModules.{w} (ringSheaf X.O))
    (b : SheafOfModules.unit (ringSheaf Y.O) ⟶ (pushforwardModules f).obj N) :
    unitTerminalHomEquiv (ringSheaf X.O) N (pushforwardUnitHomEquiv f N b) =
      pushforwardModulesUnitHomEquiv f N b := by
  rw [pushforwardUnitHomEquiv_apply, pullbackModulesObjUnitIso_hom_comp f N
    (((pullbackAdjPushforwardModules f).homEquiv _ N).symm b), Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The canonical morphism `pushforwardUnitSection f` corresponds to the identity. -/
private theorem pushforwardUnitHomEquiv_pushforwardUnitSection :
    pushforwardUnitHomEquiv f (SheafOfModules.unit (ringSheaf X.O))
      (pushforwardUnitSection f) = 𝟙 _ :=
  Equiv.apply_symm_apply _ _

end Geometric

section Composition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z)
  (χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z)
  (τ₀ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ⟶ χ.toToposHom.pushforward)
  (τ : pushforwardModules φ ⋙ pushforwardModules ψ ⟶ pushforwardModules χ)
  (hτ : ∀ N : SheafOfModules.{w} (ringSheaf X.O),
    (Sheaf.moduleSheafFunctor (ringSheaf Z.O)).map (τ.app N) =
      τ₀.app (Sheaf.moduleSheaf (ringSheaf X.O) N))

include hτ

/-- A morphism `1_{O_E} ⟶ ψ_*φ_*N` out of the free module of rank one, read through `τ` and
transposed in one step, is what transposing it in two steps gives. -/
theorem pushforwardUnitHomEquiv_natTrans (N : SheafOfModules.{w} (ringSheaf X.O))
    (b : SheafOfModules.unit (ringSheaf Z.O) ⟶
      (pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) :
    pushforwardUnitHomEquiv χ N (b ≫ τ.app N) =
      pushforwardUnitHomEquiv φ N
        (pushforwardUnitHomEquiv ψ ((pushforwardModules φ).obj N) b) := by
  refine (unitTerminalHomEquiv (ringSheaf X.O) N).injective ?_
  rw [unitTerminalHomEquiv_pushforwardUnitHomEquiv,
    unitTerminalHomEquiv_pushforwardUnitHomEquiv]
  have hL : pushforwardModulesUnitHomEquiv χ N (b ≫ τ.app N) =
      χ.toToposHom.pushforwardTerminalHomEquiv (Sheaf.moduleSheaf (ringSheaf X.O) N)
        (unitTerminalHomEquiv (ringSheaf Z.O) ((pushforwardModules χ).obj N)
          (b ≫ τ.app N)) := rfl
  have hR : pushforwardModulesUnitHomEquiv φ N
        (pushforwardUnitHomEquiv ψ ((pushforwardModules φ).obj N) b) =
      φ.toToposHom.pushforwardTerminalHomEquiv (Sheaf.moduleSheaf (ringSheaf X.O) N)
        (unitTerminalHomEquiv (ringSheaf Y.O) ((pushforwardModules φ).obj N)
          (pushforwardUnitHomEquiv ψ ((pushforwardModules φ).obj N) b)) := rfl
  rw [hL, hR, unitTerminalHomEquiv_pushforwardUnitHomEquiv]
  have hI : pushforwardModulesUnitHomEquiv ψ ((pushforwardModules φ).obj N) b =
      ψ.toToposHom.pushforwardTerminalHomEquiv
          (Sheaf.moduleSheaf (ringSheaf Y.O) ((pushforwardModules φ).obj N))
        (unitTerminalHomEquiv (ringSheaf Z.O)
          ((pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) b) := rfl
  rw [hI, unitTerminalHomEquiv_comp, hτ N]
  exact MorphismOfTopoi.pushforwardTerminalHomEquiv_natTrans φ.toToposHom ψ.toToposHom
    χ.toToposHom τ₀ (Sheaf.moduleSheaf (ringSheaf X.O) N) _

/-- The canonical morphisms `1_{O_D} ⟶ f_*1_{O_C}` of
`Stacks.Cohomology.SiteModules.pushforwardUnitSection` are compatible with a composite: the one
for `ψ` followed by the direct image of the one for `φ` and then by `τ` is the one for `χ`. -/
theorem pushforwardUnitSection_natTrans :
    pushforwardUnitSection ψ ≫
        (pushforwardModules ψ).map (pushforwardUnitSection φ) ≫
        τ.app (SheafOfModules.unit (ringSheaf X.O)) =
      pushforwardUnitSection χ := by
  refine (pushforwardUnitHomEquiv χ (SheafOfModules.unit (ringSheaf X.O))).injective ?_
  rw [pushforwardUnitHomEquiv_pushforwardUnitSection, ← Category.assoc,
    pushforwardUnitHomEquiv_natTrans φ ψ χ τ₀ τ hτ,
    pushforwardUnitHomEquiv_comp ψ (pushforwardUnitSection φ) (pushforwardUnitSection ψ),
    pushforwardUnitHomEquiv_pushforwardUnitSection, Category.id_comp,
    pushforwardUnitHomEquiv_pushforwardUnitSection]

/-- If `τ` presents `χ` as a composite of `φ` and `ψ` — a natural transformation
`φ_* ⋙ ψ_* ⟶ χ_*` of direct images of `𝒪`-modules whose underlying map of sheaves of sets is
`τ₀` — then the ring map `Γ(E, O_E) ⟶ Γ(C, O_C)` of `χ` is the composite of the ring maps of `ψ`
and of `φ`. -/
theorem globalSectionsRingHom_natTrans :
    globalSectionsRingHom χ = (globalSectionsRingHom φ).comp (globalSectionsRingHom ψ) := by
  refine RingHom.ext fun a ↦ (unitEndEquiv (ringSheaf X.O)).injective ?_
  change unitEnd (ringSheaf X.O) (globalSectionsRingHom χ a) =
    unitEnd (ringSheaf X.O) (globalSectionsRingHom φ (globalSectionsRingHom ψ a))
  rw [unitEnd_globalSectionsRingHom, unitEnd_globalSectionsRingHom, pushforwardUnitEndMap_eq,
    pushforwardUnitEndMap_eq, unitEnd_globalSectionsRingHom, pushforwardUnitEndMap_eq,
    ← pushforwardUnitHomEquiv_comp ψ (pushforwardUnitSection φ)
      (unitEnd (ringSheaf Z.O) a ≫ pushforwardUnitSection ψ),
    ← pushforwardUnitHomEquiv_natTrans φ ψ χ τ₀ τ hτ]
  simp only [Category.assoc, pushforwardUnitSection_natTrans φ ψ χ τ₀ τ hτ]

end Composition

end Stacks.Cohomology.SiteModules

end
