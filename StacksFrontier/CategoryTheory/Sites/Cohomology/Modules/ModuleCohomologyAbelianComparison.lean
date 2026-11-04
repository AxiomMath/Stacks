module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.BiggerSiteModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of a sheaf of modules is the cohomology of its underlying abelian sheaf

Let `(C, J)` be a site with a terminal object `T` and let `R` be a sheaf of rings on it, with
its sections and the module sections in a universe containing the site. For every sheaf of
`R`-modules `M` and every degree `n`, the cohomology of `M` computed in the category of sheaves
of `R`-modules — `Ext^n(R, M)`, `Stacks.Cohomology.BiggerSiteModules.moduleFunctorH` — is the
cohomology of its underlying abelian sheaf — `Ext^n(ℤ, M)`, Mathlib's
`CategoryTheory.Sheaf.H` — naturally in `M`. This is Stacks 03FD for global sections, for a
site whose objects need not form a small type.

## Main definitions

* `Stacks.Cohomology.ModuleAbelianComparison.unitHomAddEquivOfIsTerminal`: a morphism out of the
  unit sheaf of modules is its value at `1` over the terminal object.
* `Stacks.Cohomology.ModuleAbelianComparison.unitCoyonedaIsoOfIsTerminal`: in degree zero, maps
  out of `R` and maps out of the constant sheaf `ℤ` into the underlying abelian sheaf agree.
* `Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIsoOfIsTerminal`: the comparison in
  every degree.

## Implementation notes

The proof is the `δ`-functor argument of the source, in the form
`ModuleSheafCohomology.extComparisonIso`: the forgetful functor `SheafOfModules.toSheaf R` is
exact, the two degree-zero functors are identified through the sections over `T`, and the
underlying abelian sheaf of an injective sheaf of modules has no higher `Ext` out of the
constant sheaf `ℤ`, which is sectionwise torsion free
(`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`).

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u

namespace Stacks.Cohomology.ModuleAbelianComparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{max u v w})

attribute [local instance] Stacks.Cohomology.BiggerSiteModules.hasSheafify_source
  Stacks.Cohomology.BiggerSiteModules.wEqualsLocallyBijective_source

/-- The category of abelian sheaves on `J`, in the universe of the modules, has `Ext` groups. -/
local instance hasExt : HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max u v w}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u, v, w} (J := J)

/-- The category of abelian sheaves on `J`, in the universe of the modules, has enough
injectives. -/
@[sga "4 V 0.2.1" "abelian sheaves on sites"]
local instance enoughInjectives : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v w}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u, v, w} (J := J)

variable {T : C} (hT : IsTerminal T)

/-- **A morphism out of the unit sheaf of modules is a section over the terminal object.** For a
sheaf of `R`-modules `M` on a site with a terminal object `T`, the map `φ ↦ φ(1)`, evaluated over
`T`, is an additive bijection from `Hom(R, M)` to `M(T)`: a morphism out of `R` is a global
section (`CategoryTheory.SheafOfModules.unitHomEquiv`), and a global section is determined by its
value over `T`, every object mapping uniquely to `T`. -/
def unitHomAddEquivOfIsTerminal (M : SheafOfModules.{max u v w} R) :
    (SheafOfModules.unit R ⟶ M) ≃+ M.val.presheaf.obj (op T) := by
  let σ : M.sections → M.val.presheaf.obj (op T) := fun s => s.eval (op T)
  have hσ : Function.Bijective σ := by
    constructor
    · intro s s' h
      apply Subtype.ext
      funext X
      have hs := s.2 (hT.from X.unop).op
      have hs' := s'.2 (hT.from X.unop).op
      change M.val.presheaf.map (hT.from X.unop).op (s.eval (op T)) = s.eval X at hs
      change M.val.presheaf.map (hT.from X.unop).op (s'.eval (op T)) = s'.eval X at hs'
      change s.eval X = s'.eval X
      rw [← hs, ← hs']
      exact congrArg _ h
    · intro m
      refine ⟨⟨fun X => M.val.presheaf.map (hT.from X.unop).op m, ?_⟩, ?_⟩
      · intro X Y f
        change M.val.presheaf.map f (M.val.presheaf.map (hT.from X.unop).op m) =
          M.val.presheaf.map (hT.from Y.unop).op m
        have e : (hT.from X.unop).op ≫ f = (hT.from Y.unop).op :=
          Quiver.Hom.unop_inj (hT.hom_ext _ _)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, e]
      · change M.val.presheaf.map (hT.from T).op m = m
        rw [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, M.val.presheaf.map_id]
        rfl
  let f : (SheafOfModules.unit R ⟶ M) →+ M.val.presheaf.obj (op T) :=
    { toFun φ := σ (M.unitHomEquiv φ)
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact AddEquiv.ofBijective f (hσ.comp M.unitHomEquiv.bijective)

/-- `unitHomAddEquivOfIsTerminal` sends a morphism `φ : R ⟶ M` to the value of `φ` at `1` over
the terminal object `T`. -/
@[simp]
lemma unitHomAddEquivOfIsTerminal_apply (M : SheafOfModules.{max u v w} R)
    (φ : SheafOfModules.unit R ⟶ M) :
    unitHomAddEquivOfIsTerminal J R hT M φ = φ.val.app (op T) (1 : R.obj.obj (op T)) :=
  rfl

/-- The constant sheaf `ℤ` on a site, with values in the universe of the modules. -/
abbrev constantZ : Sheaf J AddCommGrpCat.{max u v w} :=
  (constantSheaf J AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))

/-- A morphism out of the constant sheaf `ℤ` into an abelian sheaf is a section over the terminal
object, by the adjunction between the constant sheaf and sections over `T`. -/
def constantHomAddEquivOfIsTerminal (F : Sheaf J AddCommGrpCat.{max u v w}) :
    (constantZ J ⟶ F) ≃+ F.obj.obj (op T) :=
  ((constantSheafAdj J AddCommGrpCat.{max u v w} hT).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- `constantHomAddEquivOfIsTerminal` is natural in the abelian sheaf: the section over `T`
corresponding to `a ≫ g` is the image under `g` of the section corresponding to `a`. -/
lemma constantHomAddEquivOfIsTerminal_comp {F G : Sheaf J AddCommGrpCat.{max u v w}}
    (a : constantZ J ⟶ F) (g : F ⟶ G) :
    constantHomAddEquivOfIsTerminal J hT G (a ≫ g) =
      g.hom.app (op T) (constantHomAddEquivOfIsTerminal J hT F a) := by
  simp only [constantHomAddEquivOfIsTerminal, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- **Stacks 03FD in degree zero, at a terminal object.** Morphisms out of the structure sheaf
`R` and morphisms out of the constant sheaf `ℤ` into the underlying abelian sheaf are the same
functor of the sheaf of `R`-modules: both are the sections over the terminal object. -/
def unitCoyonedaIsoOfIsTerminal :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      SheafOfModules.toSheaf.{max u v w} R ⋙ preadditiveCoyoneda.obj (op (constantZ J)) :=
  NatIso.ofComponents (fun M => (unitHomAddEquivOfIsTerminal J R hT M).toAddCommGrpIso)
      (fun {M N} f => by
        ext φ
        rfl) ≪≫
    (NatIso.ofComponents (G := SheafOfModules.toSheaf.{max u v w} R ⋙
        (sheafSections J AddCommGrpCat.{max u v w}).obj (op T))
      (fun M => (constantHomAddEquivOfIsTerminal J hT
        ((SheafOfModules.toSheaf R).obj M)).toAddCommGrpIso)
      (fun {M N} f => by
        ext φ
        exact constantHomAddEquivOfIsTerminal_comp J hT φ
          ((SheafOfModules.toSheaf R).map f))).symm

/-- The constant sheaf `ℤ` is sectionwise torsion free. -/
lemma constantZ_isTorsionFree (X : Cᵒᵖ) :
    Module.IsTorsionFree ℤ ((constantZ.{w} J).obj.obj X) :=
  ModuleSheafCohomology.isTorsionFree_sheafify.{u, v, max u v w} J _ (fun _ => by
      show Module.IsTorsionFree ℤ (ULift ℤ)
      exact Module.Flat.isTorsionFree) X

/-- **Stacks 03FD, global cohomology, at a terminal object.** On a site with a terminal object,
for every degree `n` the cohomology `Ext^n(R, M)` of a sheaf of `R`-modules is the cohomology
`H^n(C, M)` of its underlying abelian sheaf, naturally in `M`.

Both sides are `δ`-functors on sheaves of `R`-modules — the second because forgetting to abelian
sheaves is exact — they agree in degree zero by `unitCoyonedaIsoOfIsTerminal`, and both are
universal: the second because the underlying abelian sheaf of an injective sheaf of modules has
no higher `Ext` out of the sectionwise torsion-free sheaf `ℤ`. -/
@[sga "7 IX 9.4.3" "(a), special case"]
def moduleFunctorHIsoOfIsTerminal (n : ℕ) :
    Stacks.Cohomology.BiggerSiteModules.moduleFunctorH.{w, v, u} J R n ≅
      SheafOfModules.toSheaf.{max u v w} R ⋙ Sheaf.functorH.{max u v w} J n := by
  haveI := Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits (J := J) R
  have h : ∀ (I : SheafOfModules.{max u v w} R) [Injective I] (m : ℕ)
      (e : Ext (constantZ.{w} J) ((SheafOfModules.toSheaf R).obj I) (m + 1)), e = 0 :=
    fun I _ m e => Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree J R I _
      (constantZ_isTorsionFree J) m e
  exact ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R) (constantZ.{w} J)
    (SheafOfModules.unit R) h (unitCoyonedaIsoOfIsTerminal J R hT) n

end Stacks.Cohomology.ModuleAbelianComparison
