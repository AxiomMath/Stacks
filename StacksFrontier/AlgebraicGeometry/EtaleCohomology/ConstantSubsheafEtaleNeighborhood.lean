module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafSliceSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleOpenSubobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant

/-!
# A subsheaf of a constant sheaf of modules is constant on an étale neighbourhood

Let `Y` be an irreducible locally Noetherian scheme in a big étale site, let `Λ` be a Noetherian
ring, let `M` be a finitely generated `Λ`-module and let `G` be a sheaf of `Λ`-modules on the
small étale site of `Y` with a monomorphism `j : G ⟶ M̲` into the constant sheaf on `M`. Then
there is an object `U₀` of the small étale site of `Y`, with nonempty underlying scheme, and a
finitely generated submodule `N ≤ M` such that the restriction of `G` to the localized site at
`U₀` is the constant sheaf on `N`.

The argument replaces the generic-stalk computation of Stacks 09BG by a maximality argument,
which is what makes it elementary. For an object `U` whose underlying scheme is irreducible the
canonical map `M ⟶ M̲(U)` is bijective
(`AlgebraicGeometry.SmallEtale.bijective_toSheafify_const_app_of_irreducibleSpace`), so the
sections of `G` over `U` cut out a submodule `constSections U ≤ M`: the constants which are
already sections of `G` there. That submodule only grows as `U` shrinks, and `M` is a Noetherian
module, so some irreducible `U₀` makes it maximal. Put `N := constSections U₀`.

On the localized site at `U₀` the inclusion of `N` is then an isomorphism onto `G`, and this is
checked by local bijectivity rather than on a stalk.

* *Local injectivity* is formal: the comparison composed with the map into `M̲` is the constant
  sheaf on the injection `N ⟶ M`, which is locally injective.
* *Local surjectivity* is the maximality. A section of `G` over an object `W` of the localized
  site is, on a covering, the image of a constant `a ∈ M`; if `W` is nonempty it contains an
  irreducible open subobject `W'` lying over `U₀`
  (`AlgebraicGeometry.SmallEtale.exists_irreducibleSpace_openObj`), and `a ∈ constSections W'`,
  which equals `N` by maximality. The section is then the image of `a` because the map into `M̲`
  is injective on sections. On a sheaf theoretically empty `W` the empty sieve covers, so there
  is nothing to check.

Only finitely many elements of `M` ever have to be realised at once — in fact only one at a time
— so no filtered-colimit lifting and no finite presentation of `M` is needed.

## Main definitions

* `AlgebraicGeometry.constSections` — the constants of `M` which over an object of the small
  étale site are already the image of a section of `G`.
* `AlgebraicGeometry.sliceConst`, `AlgebraicGeometry.sliceHom`, `AlgebraicGeometry.sliceCompare`
  — the three morphisms of the localized site at `U₀` the argument is phrased with.

## Main results

* `AlgebraicGeometry.exists_maximal_constSections` — maximality of the realised constants over
  some irreducible object.
* `AlgebraicGeometry.isLocallyInjective_sliceCompare` and
  `AlgebraicGeometry.isLocallySurjective_sliceCompare` — the two halves of local bijectivity.
* `AlgebraicGeometry.exists_constantSheafIso_overPullback_of_mono` — the restriction of `G` to
  the localized site at some nonempty `U₀` is the constant sheaf on a finitely generated `N`.

## Implementation notes

The conclusion is stated in the shape `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant` asks of
a trivializing object, namely an isomorphism of the constant sheaf on the localized site at `U₀`
with the restriction of `G` there. The translation to an isomorphism on the small étale site of
the scheme `U₀` is
`AlgebraicGeometry.nonempty_constantSheafIso_over_iff` and is not performed here.

Stacks 09BG identifies a sheaf squeezed between two constant sheaves on an irreducible scheme,
with prescribed generic stalk, with the smaller constant sheaf. The statement proved here is
different: it asserts the *existence* of the neighbourhood `U₀` and of the module `N`, and it is
an input to Stacks 09BH (3).

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.ConstantSheaf

variable (B : BigEtaleSite.{u}) (Y : B.Scheme) (Λ : Type (u + 1)) [CommRing Λ]

variable (M : ModuleCat.{u + 1} Λ)
  {G : Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ)}
  (j : G ⟶ (constantSheaf (SmallEtale.topology B Y.obj Y.property)
    (ModuleCat.{u + 1} Λ)).obj M)

/-- The constants of `M` which over `U` are the image of a section of `G`. -/
def constSections (U : SmallEtale B Y.obj Y.property) : Submodule Λ M :=
  Submodule.comap ((toSheafify (SmallEtale.topology B Y.obj Y.property)
      ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U)).hom
    (LinearMap.range (j.hom.app (op U)).hom)

/-- A constant `a` lies in `constSections U` exactly when some section of `G` over `U` maps to
the image of `a` in the sections of the constant sheaf. -/
theorem mem_constSections_iff (U : SmallEtale B Y.obj Y.property) (a : M) :
    a ∈ constSections B Y Λ M j U ↔ ∃ g : G.obj.obj (op U), j.hom.app (op U) g =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U) a :=
  Iff.rfl

/-- The canonical map from `M` to the sections of the constant sheaf commutes with restriction,
the constant presheaf having identity restriction maps. -/
theorem toSheafify_const_restrict {U U' : SmallEtale B Y.obj Y.property} (k : U' ⟶ U)
    (a : M) :
    ((constantSheaf (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{u + 1} Λ)).obj M).obj.map k.op
        ((toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U) a) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U') a :=
  (NatTrans.naturality_apply (toSheafify (SmallEtale.topology B Y.obj Y.property)
    ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)) k.op a).symm

/-- Constants realised over an object are realised over any object above it. -/
theorem constSections_le {U U' : SmallEtale B Y.obj Y.property} (k : U' ⟶ U) :
    constSections B Y Λ M j U ≤ constSections B Y Λ M j U' := by
  intro a ha
  rw [mem_constSections_iff] at ha ⊢
  obtain ⟨g, hg⟩ := ha
  refine ⟨G.obj.map k.op g, ?_⟩
  rw [NatTrans.naturality_apply j.hom k.op g, hg, toSheafify_const_restrict]

/-- **A maximal object for the constants realised over it.** Among the irreducible objects of
the small étale site of an irreducible scheme there is one over which the realised constants
form a maximal submodule of `M`; this uses that `M` is a Noetherian module. -/
theorem exists_maximal_constSections [IsNoetherianRing Λ] (hM : ModuleCat.isFG Λ M)
    [IrreducibleSpace Y.obj] :
    ∃ U₀ : SmallEtale B Y.obj Y.property,
      IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj U₀) ∧
      ∀ U : SmallEtale B Y.obj Y.property,
        IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj U) →
        ¬ constSections B Y Λ M j U₀ < constSections B Y Λ M j U := by
  have hfin : Module.Finite Λ M := hM
  have hfinal : IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj
      (SmallEtale.final B Y.obj Y.property)) := ‹IrreducibleSpace Y.obj›
  obtain ⟨P, ⟨U₀, hU₀, hP⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr inferInstance
      {P : Submodule Λ M | ∃ U : SmallEtale B Y.obj Y.property,
        IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj U) ∧
          P = constSections B Y Λ M j U}
      ⟨_, _, hfinal, rfl⟩
  exact ⟨U₀, hU₀, fun U hU => hP ▸ hmax _ ⟨U, hU, rfl⟩⟩

/-- Pointwise form of an equation `f ≫ g = h` of morphisms of modules. -/
private theorem apply_comp_eq_of_comp_eq {R : Type (u + 1)} [CommRing R]
    {X Y Z : ModuleCat.{u + 1} R} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (x : X) :
    g (f x) = h x :=
  (ConcreteCategory.comp_apply f g x).symm.trans (ConcreteCategory.congr_hom e x)

section Slice

variable (U₀ : SmallEtale B Y.obj Y.property)

/-- The comparison of the constant sheaf on the slice site at `U₀` with the restriction of the
constant sheaf. -/
abbrev sliceConst : (constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
      (ModuleCat.{u + 1} Λ)).obj M ≅
    ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{u + 1} Λ) U₀).obj
      ((constantSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ)).obj M) :=
  (overPullbackConstantSheafIso (SmallEtale.topology B Y.obj Y.property)
    (ModuleCat.{u + 1} Λ) U₀).app M

/-- The restriction to the slice site at `U₀` of a map into a constant sheaf, read as a map into
the constant sheaf of the slice site. -/
abbrev sliceHom :
    ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{u + 1} Λ) U₀).obj G ⟶
      (constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
        (ModuleCat.{u + 1} Λ)).obj M :=
  ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{u + 1} Λ) U₀).map j ≫
    (sliceConst B Y Λ M U₀).inv

/-- The comparison carries the slice-relative map into the constant sheaf back to the original
map. -/
theorem sliceConst_sliceHom_app (W : Over U₀) (g : G.obj.obj (op W.left)) :
    (sliceConst B Y Λ M U₀).hom.hom.app (op W)
        ((sliceHom B Y Λ M j U₀).hom.app (op W) g) = j.hom.app (op W.left) g := by
  have e0 : sliceHom B Y Λ M j U₀ ≫ (sliceConst B Y Λ M U₀).hom =
      ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{u + 1} Λ) U₀).map j := by
    simp [sliceHom]
  have e1 : (sliceHom B Y Λ M j U₀).hom.app (op W) ≫
      (sliceConst B Y Λ M U₀).hom.hom.app (op W) =
      (((SmallEtale.topology B Y.obj Y.property).overPullback
        (ModuleCat.{u + 1} Λ) U₀).map j).hom.app (op W) := by
    rw [← e0]
    rfl
  exact (ConcreteCategory.comp_apply _ _ g).symm.trans (ConcreteCategory.congr_hom e1 g)

/-- The comparison carries the canonical map from `M` on the slice site to the canonical map on
the small étale site. -/
theorem sliceConst_toSheafify_app (W : Over U₀) (a : M) :
    (sliceConst B Y Λ M U₀).hom.hom.app (op W)
        ((toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
          ((Functor.const (Over U₀)ᵒᵖ).obj M)).app (op W) a) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op W.left) a :=
  apply_comp_eq_of_comp_eq
    (Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso_app
      (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ) U₀ M (op W)) a

/-- If `j` is injective on sections over every object, then so is its restriction to the slice
site at `U₀`. -/
theorem injective_sliceHom_app (hj : ∀ U : SmallEtale B Y.obj Y.property,
    Function.Injective (j.hom.app (op U))) (W : Over U₀) :
    Function.Injective ((sliceHom B Y Λ M j U₀).hom.app (op W)) := by
  intro x y hxy
  refine hj W.left ?_
  rw [← sliceConst_sliceHom_app B Y Λ M j U₀ W x, ← sliceConst_sliceHom_app B Y Λ M j U₀ W y,
    hxy]

/-- Over an object of the slice site at `U₀`, a section of `G` has constant image `a` exactly
when it does over the underlying object of the small étale site. -/
theorem sliceHom_eq_iff_mem_constSections (W : Over U₀) (a : M)
    (g : G.obj.obj (op W.left)) :
    (sliceHom B Y Λ M j U₀).hom.app (op W) g =
        (toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
          ((Functor.const (Over U₀)ᵒᵖ).obj M)).app (op W) a ↔
      j.hom.app (op W.left) g =
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op W.left) a := by
  have hinj : Function.Injective ((sliceConst B Y Λ M U₀).hom.hom.app (op W)) :=
    ((ConcreteCategory.isIso_iff_bijective _).1
      (inferInstance : IsIso ((sliceConst B Y Λ M U₀).hom.hom.app (op W)))).1
  constructor
  · intro h
    rw [← sliceConst_sliceHom_app B Y Λ M j U₀ W g, h, sliceConst_toSheafify_app]
  · intro h
    refine hinj ?_
    rwa [sliceConst_sliceHom_app, sliceConst_toSheafify_app]

end Slice

section Core

variable [IsNoetherianRing Λ] [IrreducibleSpace Y.obj] [IsLocallyNoetherian Y.obj]

/-- The comparison morphism from the constant sheaf on `N` over the slice site at `U₀`. -/
abbrev sliceCompare (U₀ : SmallEtale B Y.obj Y.property) (NC : ModuleCat.{u + 1} Λ)
    (φ : NC ⟶ G.obj.obj (op U₀)) :
    (constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
        (ModuleCat.{u + 1} Λ)).obj NC ⟶
      ((SmallEtale.topology B Y.obj Y.property).overPullback (ModuleCat.{u + 1} Λ) U₀).obj G :=
  ((constantSheafAdj ((SmallEtale.topology B Y.obj Y.property).over U₀)
    (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U₀))).homEquiv NC _).symm φ

omit [IsNoetherianRing Λ] [IrreducibleSpace Y.obj] [IsLocallyNoetherian Y.obj] in
/-- The comparison morphism composed with the map into the constant sheaf on `M` is the constant
sheaf on the inclusion `N ⟶ M`. -/
theorem sliceCompare_comp (U₀ : SmallEtale B Y.obj Y.property) (NC : ModuleCat.{u + 1} Λ)
    (mm : NC ⟶ M) (φ : NC ⟶ G.obj.obj (op U₀))
    (hφ : ∀ n : NC, j.hom.app (op U₀) (φ n) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U₀) (mm n)) :
    sliceCompare B Y Λ U₀ NC φ ≫ sliceHom B Y Λ M j U₀ =
      (constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
        (ModuleCat.{u + 1} Λ)).map mm := by
  refine ((constantSheafAdj ((SmallEtale.topology B Y.obj Y.property).over U₀)
    (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U₀))).homEquiv NC _).injective ?_
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply,
    ← Stacks.ConstantSheaf.toSheafify_const_naturality_app]
  have hi : (constantSheafAdj ((SmallEtale.topology B Y.obj Y.property).over U₀)
      (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U₀))).homEquiv NC _
      (sliceCompare B Y Λ U₀ NC φ) = φ := Equiv.apply_symm_apply _ _
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply] at hi
  refine ConcreteCategory.hom_ext _ _ fun n => ?_
  have hin : (sliceCompare B Y Λ U₀ NC φ).hom.app (op (Over.mk (𝟙 U₀)))
      ((toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
        ((Functor.const (Over U₀)ᵒᵖ).obj NC)).app (op (Over.mk (𝟙 U₀))) n) = φ n :=
    apply_comp_eq_of_comp_eq hi n
  refine (ConcreteCategory.comp_apply _ _ n).trans ?_
  refine Eq.trans (ConcreteCategory.comp_apply
    ((sliceCompare B Y Λ U₀ NC φ).hom.app (op (Over.mk (𝟙 U₀))))
    ((sliceHom B Y Λ M j U₀).hom.app (op (Over.mk (𝟙 U₀)))) _) ?_
  rw [hin]
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ n).symm
  exact (sliceHom_eq_iff_mem_constSections B Y Λ M j U₀ (Over.mk (𝟙 U₀)) (mm n) (φ n)).2 (hφ n)

omit [IsNoetherianRing Λ] [IrreducibleSpace Y.obj] [IsLocallyNoetherian Y.obj] in
/-- The comparison morphism is locally injective, because its composite with the map into the
constant sheaf on `M` is the constant sheaf on an injective map. -/
theorem isLocallyInjective_sliceCompare (U₀ : SmallEtale B Y.obj Y.property)
    (NC : ModuleCat.{u + 1} Λ) (mm : NC ⟶ M) (hminj : Function.Injective mm)
    (φ : NC ⟶ G.obj.obj (op U₀))
    (hφ : ∀ n : NC, j.hom.app (op U₀) (φ n) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U₀) (mm n)) :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B Y.obj Y.property).over U₀)
      (sliceCompare B Y Λ U₀ NC φ).hom := by
  have hlocComp : Presheaf.IsLocallyInjective ((SmallEtale.topology B Y.obj Y.property).over U₀)
      ((sliceCompare B Y Λ U₀ NC φ).hom ≫ (sliceHom B Y Λ M j U₀).hom) := by
    have hEq : (sliceCompare B Y Λ U₀ NC φ).hom ≫ (sliceHom B Y Λ M j U₀).hom =
        ((presheafToSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
          (ModuleCat.{u + 1} Λ)).map ((Functor.const (Over U₀)ᵒᵖ).map mm)).hom :=
      congrArg (fun t => t.hom) (sliceCompare_comp B Y Λ M j U₀ NC mm φ hφ)
    rw [hEq]
    exact (Presheaf.isLocallyInjective_presheafToSheaf_map_iff
      (J := (SmallEtale.topology B Y.obj Y.property).over U₀)
      ((Functor.const (Over U₀)ᵒᵖ).map mm)).2
      (Presheaf.isLocallyInjective_of_injective _ _ fun _ => hminj)
  exact Presheaf.isLocallyInjective_of_isLocallyInjective _ (sliceCompare B Y Λ U₀ NC φ).hom
    (sliceHom B Y Λ M j U₀).hom

omit [IsNoetherianRing Λ] in
/-- The comparison morphism is locally surjective: a section of `G` over an object of the slice
site has a constant image there, and that constant lies in `N` because the object can be shrunk
to a nonempty irreducible one, over which the realised constants are already `N`. -/
theorem isLocallySurjective_sliceCompare
    (U₀ : SmallEtale B Y.obj Y.property) (NC : ModuleCat.{u + 1} Λ) (mm : NC ⟶ M)
    (φ : NC ⟶ G.obj.obj (op U₀))
    (hφ : ∀ n : NC, j.hom.app (op U₀) (φ n) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U₀) (mm n))
    (hjinj : ∀ U : SmallEtale B Y.obj Y.property, Function.Injective (j.hom.app (op U)))
    (hN : ∀ W : SmallEtale B Y.obj Y.property,
      IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj W) → (W ⟶ U₀) →
      ∀ a : M, a ∈ constSections B Y Λ M j W → ∃ n : NC, mm n = a) :
    Presheaf.IsLocallySurjective ((SmallEtale.topology B Y.obj Y.property).over U₀)
      (sliceCompare B Y Λ U₀ NC φ).hom := by
  have _ := Stacks.ConstantSheaf.isLocallySurjective_toSheafify_moduleCat.{u, u + 1, u + 1}
    ((SmallEtale.topology B Y.obj Y.property).over U₀) Λ ((Functor.const (Over U₀)ᵒᵖ).obj M)
  have hEq : ∀ W : Over U₀, (sliceCompare B Y Λ U₀ NC φ).hom.app (op W) ≫
      (sliceHom B Y Λ M j U₀).hom.app (op W) =
      ((constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
        (ModuleCat.{u + 1} Λ)).map mm).hom.app (op W) := fun W => by
    rw [← sliceCompare_comp B Y Λ M j U₀ NC mm φ hφ]
    rfl
  constructor
  intro V g
  refine ((SmallEtale.topology B Y.obj Y.property).over U₀).transitive
    (Presheaf.imageSieve_mem _ (toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
      ((Functor.const (Over U₀)ᵒᵖ).obj M)) ((sliceHom B Y Λ M j U₀).hom.app (op V) g)) _ ?_
  intro W f hf
  obtain ⟨a, ha⟩ := hf
  have hdesc : (sliceHom B Y Λ M j U₀).hom.app (op W)
      ((((SmallEtale.topology B Y.obj Y.property).overPullback
        (ModuleCat.{u + 1} Λ) U₀).obj G).obj.map f.op g) =
      (toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
        ((Functor.const (Over U₀)ᵒᵖ).obj M)).app (op W) a :=
    (NatTrans.naturality_apply (sliceHom B Y Λ M j U₀).hom f.op g).trans ha.symm
  by_cases hW : Nonempty ((SmallEtale.toScheme B Y.obj Y.property).obj W.left)
  · obtain ⟨w⟩ := hW
    have hmemW : a ∈ constSections B Y Λ M j W.left :=
      (mem_constSections_iff B Y Λ M j W.left a).2
        ⟨_, (sliceHom_eq_iff_mem_constSections B Y Λ M j U₀ W a _).1 hdesc⟩
    obtain ⟨W', hW'c, hW'irr⟩ :=
      SmallEtale.exists_irreducibleSpace_openObj B Y.obj Y.property W.left w
    have hirr2 : IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj
      (SmallEtale.openObj W.left W' hW'c)) := hW'irr
    obtain ⟨n, hn⟩ := hN _ hirr2 (SmallEtale.openObjHom W.left W' hW'c ≫ W.hom) a
      (constSections_le B Y Λ M j (SmallEtale.openObjHom W.left W' hW'c) hmemW)
    have h2 : ((constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
          (ModuleCat.{u + 1} Λ)).map mm).hom.app (op W)
        ((toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
          ((Functor.const (Over U₀)ᵒᵖ).obj NC)).app (op W) n) =
        (toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
          ((Functor.const (Over U₀)ᵒᵖ).obj M)).app (op W) (mm n) :=
      (apply_comp_eq_of_comp_eq (Stacks.ConstantSheaf.toSheafify_const_naturality_app
        ((SmallEtale.topology B Y.obj Y.property).over U₀) (ModuleCat.{u + 1} Λ) mm
        (op W)) n).symm
    have hfmem : (Presheaf.imageSieve (sliceCompare B Y Λ U₀ NC φ).hom g) f := by
      refine ⟨(toSheafify ((SmallEtale.topology B Y.obj Y.property).over U₀)
        ((Functor.const (Over U₀)ᵒᵖ).obj NC)).app (op W) n, ?_⟩
      refine injective_sliceHom_app B Y Λ M j U₀ hjinj W ?_
      refine Eq.trans ?_ hdesc.symm
      refine ((ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom (hEq W) _)).trans ?_
      rw [h2, hn]
    exact ((SmallEtale.topology B Y.obj Y.property).over U₀).superset_covering
      (fun Z k _ => Sieve.downward_closed _ hfmem k)
      (((SmallEtale.topology B Y.obj Y.property).over U₀).top_mem W)
  · refine ((SmallEtale.topology B Y.obj Y.property).over U₀).superset_covering bot_le ?_
    rw [Stacks.EtaleCohomology.bot_mem_over_iff]
    exact Stacks.EtaleCohomology.bot_mem_topology B Y.property (not_nonempty_iff.mp hW)

/-- **A subsheaf of a constant sheaf of modules becomes constant on an étale neighbourhood.** -/
theorem exists_constantSheafIso_overPullback_of_mono (hM : ModuleCat.isFG Λ M) [Mono j] :
    ∃ (U₀ : SmallEtale B Y.obj Y.property) (N : ModuleCat.{u + 1} Λ),
      Nonempty ((SmallEtale.toScheme B Y.obj Y.property).obj U₀) ∧ ModuleCat.isFG Λ N ∧
      Nonempty ((constantSheaf ((SmallEtale.topology B Y.obj Y.property).over U₀)
          (ModuleCat.{u + 1} Λ)).obj N ≅
        ((SmallEtale.topology B Y.obj Y.property).overPullback
          (ModuleCat.{u + 1} Λ) U₀).obj G) := by
  classical
  have hjinj : ∀ U : SmallEtale B Y.obj Y.property, Function.Injective (j.hom.app (op U)) :=
    fun U => (ModuleCat.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app j.hom).1 inferInstance (op U))
  obtain ⟨U₀, hU₀irr, hmax⟩ := exists_maximal_constSections B Y Λ M j hM
  have hθ := SmallEtale.bijective_toSheafify_const_app_of_irreducibleSpace B Y.obj Y.property Λ
    M U₀
  have hfin : Module.Finite Λ M := hM
  have hnoe : _root_.IsNoetherian Λ M := inferInstance
  let e := LinearEquiv.ofBijective (ModuleCat.Hom.hom
    ((toSheafify (SmallEtale.topology B Y.obj Y.property)
      ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U₀))) hθ
  let α := e.symm.toLinearMap.comp (ModuleCat.Hom.hom (j.hom.app (op U₀)))
  have hαinj : Function.Injective α := e.symm.injective.comp (hjinj U₀)
  have hrange : LinearMap.range α = constSections B Y Λ M j U₀ := by
    ext a
    rw [mem_constSections_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, (e.apply_symm_apply _).symm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.symm_apply_eq.mpr hg⟩
  refine ⟨U₀, ModuleCat.of Λ (LinearMap.range α), ⟨hU₀irr.toNonempty.some⟩,
    Module.Finite.iff_fg.2 (hnoe.noetherian _), ?_⟩
  set NC : ModuleCat.{u + 1} Λ := ModuleCat.of Λ (LinearMap.range α)
  set mm : NC ⟶ M := ModuleCat.ofHom (LinearMap.range α).subtype
  set φ : NC ⟶ G.obj.obj (op U₀) :=
    ModuleCat.ofHom (LinearEquiv.ofInjective α hαinj).symm.toLinearMap
  have hφ : ∀ n : NC, j.hom.app (op U₀) (φ n) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((Functor.const (SmallEtale B Y.obj Y.property)ᵒᵖ).obj M)).app (op U₀) (mm n) := by
    intro n
    have hval : e.symm (j.hom.app (op U₀) (φ n)) = mm n :=
      congrArg Subtype.val ((LinearEquiv.ofInjective α hαinj).apply_symm_apply n)
    exact e.symm_apply_eq.mp hval
  have hN : ∀ W : SmallEtale B Y.obj Y.property,
      IrreducibleSpace ((SmallEtale.toScheme B Y.obj Y.property).obj W) → (W ⟶ U₀) →
      ∀ a : M, a ∈ constSections B Y Λ M j W → ∃ n : NC, mm n = a := by
    intro W hWirr k a ha
    have heq : constSections B Y Λ M j U₀ = constSections B Y Λ M j W :=
      eq_of_le_of_not_lt (constSections_le B Y Λ M j k) (hmax W hWirr)
    rw [← heq, ← hrange] at ha
    exact ⟨⟨a, ha⟩, rfl⟩
  have : IsIso (sliceCompare B Y Λ U₀ NC φ) :=
    (Sheaf.isLocallyBijective_iff_isIso (sliceCompare B Y Λ U₀ NC φ)).mp
      ⟨isLocallyInjective_sliceCompare B Y Λ M j U₀ NC mm Subtype.val_injective φ hφ,
        isLocallySurjective_sliceCompare B Y Λ M j U₀ NC mm φ hφ hjinj hN⟩
  exact ⟨asIso (sliceCompare B Y Λ U₀ NC φ)⟩

end Core

end AlgebraicGeometry

end
